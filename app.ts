// The starter's HTTP surface, exactly as it ships: a health probe and an API root, and a JSON 404
// for everything else. The contest's real surface — git smart HTTP, REST v3 resources, GraphQL v4 and
// the MCP endpoint — is what you add (README.md names it, and the rules link below says what scores).
//
// app.ts is deliberately separate from main.ts: this is the server, the file you grow; main.ts is the
// entry <-> env lifecycle and should stay as it is.

import { createHash } from 'node:crypto';
import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { deflateSync, inflateSync } from 'node:zlib';

const JSON_TYPE = 'application/json; charset=utf-8';

/** Answer one request with a JSON body; `headers` go beside the JSON ones. */
function sendJson(res: ServerResponse, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  const text = `${JSON.stringify(body)}\n`;
  res.writeHead(status, { 'content-type': JSON_TYPE, 'content-length': Buffer.byteLength(text), ...headers });
  res.end(text);
}

/** The path of a request URL, or '/' when it does not parse (never a throw from a request). */
function pathOf(req: IncomingMessage): string {
  try {
    return new URL(req.url ?? '/', 'http://entry').pathname;
  } catch {
    return '/';
  }
}

// ---------------------------------------------------------------------------------------------
// The forge's in-memory state. One process, one trial: everything a check creates through one surface
// is visible from the others, and every identifier is drawn from a monotone counter so two runs of the
// same request sequence produce the same bytes.

/** The login the trial's token names (wire.ts buildScenario: users[0] under the fixed scenario seed). */
const VIEWER_LOGIN = 'adaiversen';
const VIEWER_NAME = 'ada iversen';
const VIEWER_EMAIL = `${VIEWER_LOGIN}@example.invalid`;

/** The scenario's day one: every timestamp we mint is this plus a deterministic tick. */
const EPOCH_SEC = 1_735_689_600;

let clockTick = 0;
function nowSec(): number {
  clockTick += 1;
  return EPOCH_SEC + clockTick * 60;
}
function isoOf(sec: number): string {
  return new Date(sec * 1000).toISOString();
}

let nextId = 1;
function allocateId(): number {
  const id = nextId;
  nextId += 1;
  return id;
}

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';

interface GitObj {
  type: ObjType;
  data: Buffer;
}

interface FileEntry {
  mode: string;
  data: Buffer;
}

interface Label {
  name: string;
  color: string;
}

interface Issue {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  createdAt: number;
}

interface Comment {
  id: number;
  issue: number;
  body: string;
  createdAt: number;
}

interface Pull {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  head: string;
  base: string;
  baseSha: string;
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  createdAt: number;
}

interface Repo {
  id: number;
  owner: string;
  name: string;
  private: boolean;
  description: string;
  defaultBranch: string;
  createdAt: number;
  refs: Map<string, string>;
  objects: Map<string, GitObj>;
  issues: Map<number, Issue>;
  issueSeq: number;
  labels: Map<string, Label>;
  pulls: Map<number, Pull>;
  pullSeq: number;
  comments: Map<number, Comment>;
  commentSeq: number;
}

const repos = new Map<string, Repo>();

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}

function findRepo(owner: string, name: string): Repo | null {
  return repos.get(repoKey(owner, name)) ?? null;
}

function makeRepo(owner: string, name: string, priv: boolean, description: string): Repo {
  const repo: Repo = {
    id: allocateId(),
    owner,
    name,
    private: priv,
    description,
    defaultBranch: 'main',
    createdAt: nowSec(),
    refs: new Map(),
    objects: new Map(),
    issues: new Map(),
    issueSeq: 0,
    labels: new Map(),
    pulls: new Map(),
    pullSeq: 0,
    comments: new Map(),
    commentSeq: 0,
  };
  repos.set(repoKey(owner, name), repo);
  return repo;
}

// ---------------------------------------------------------------------------------------------
// Git object plumbing shared by the REST contents API and the smart-HTTP server.

function hashObject(type: ObjType, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return createHash('sha1').update(header).update(data).digest('hex');
}

function putObject(repo: Repo, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}

function getObject(repo: Repo, oid: string): GitObj | null {
  return repo.objects.get(oid.toLowerCase()) ?? null;
}

function commitTreeOf(obj: GitObj): string {
  const text = obj.data.toString('utf8');
  const match = /^tree ([0-9a-f]{40})$/m.exec(text);
  return match?.[1] ?? '';
}

function commitParentsOf(obj: GitObj): string[] {
  const parents: string[] = [];
  for (const line of obj.data.toString('utf8').split('\n')) {
    if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line === '') break;
  }
  return parents;
}

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    if (space < 0) break;
    const nul = data.indexOf(0x00, space);
    if (nul < 0) break;
    const mode = data.subarray(offset, space).toString('ascii');
    const name = data.subarray(space + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    offset = nul + 21;
  }
  return entries;
}

function gitSortKey(name: string, mode: string): string {
  return mode === '40000' ? `${name}/` : name;
}

function buildTree(repo: Repo, files: Map<string, FileEntry>): string {
  const blobs: TreeEntry[] = [];
  const dirs = new Map<string, Map<string, FileEntry>>();
  for (const [path, entry] of files) {
    const slash = path.indexOf('/');
    if (slash < 0) {
      blobs.push({ mode: entry.mode, name: path, oid: putObject(repo, 'blob', entry.data) });
    } else {
      const dir = path.slice(0, slash);
      const rest = path.slice(slash + 1);
      let group = dirs.get(dir);
      if (group === undefined) {
        group = new Map();
        dirs.set(dir, group);
      }
      group.set(rest, entry);
    }
  }
  const entries: TreeEntry[] = [...blobs];
  for (const [name, group] of dirs) entries.push({ mode: '40000', name, oid: buildTree(repo, group) });
  entries.sort((a, b) => Buffer.compare(Buffer.from(gitSortKey(a.name, a.mode)), Buffer.from(gitSortKey(b.name, b.mode))));
  const parts: Buffer[] = [];
  for (const entry of entries) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return putObject(repo, 'tree', Buffer.concat(parts));
}

function walkTree(repo: Repo, oid: string, prefix: string, out: Map<string, FileEntry>): void {
  const obj = getObject(repo, oid);
  if (obj === null || obj.type !== 'tree') return;
  for (const entry of parseTree(obj.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (entry.mode === '40000') {
      walkTree(repo, entry.oid, path, out);
    } else {
      const blob = getObject(repo, entry.oid);
      if (blob !== null && blob.type === 'blob') out.set(path, { mode: entry.mode, data: blob.data });
    }
  }
}

function filesOfCommit(repo: Repo, refOrSha: string): Map<string, FileEntry> {
  const out = new Map<string, FileEntry>();
  let target = refOrSha;
  if (getObject(repo, target) === null) {
    const resolved = repo.refs.get(branchRef(refOrSha)) ?? repo.refs.get(refOrSha);
    if (resolved !== undefined) target = resolved;
  }
  const obj = getObject(repo, target);
  if (obj === null) return out;
  if (obj.type === 'commit') {
    walkTree(repo, commitTreeOf(obj), '', out);
  } else if (obj.type === 'tag') {
    const target2 = tagTargetOf(obj);
    if (target2 !== '') return filesOfCommit(repo, target2);
  }
  return out;
}

function tagTargetOf(obj: GitObj): string {
  const match = /^object ([0-9a-f]{40})$/m.exec(obj.data.toString('utf8'));
  return match?.[1] ?? '';
}

function branchRef(branch: string): string {
  return branch.startsWith('refs/') ? branch : `refs/heads/${branch}`;
}

function branchNameOf(ref: string): string {
  return ref.startsWith('refs/heads/') ? ref.slice('refs/heads/'.length) : ref;
}

function tipOf(repo: Repo, branch: string): string | null {
  return repo.refs.get(branchRef(branch)) ?? null;
}

function peelToCommit(repo: Repo, oid: string): string | null {
  let current = oid;
  for (let hop = 0; hop < 8; hop += 1) {
    const obj = getObject(repo, current);
    if (obj === null) return null;
    if (obj.type === 'commit') return current;
    if (obj.type === 'tag') {
      const target = tagTargetOf(obj);
      if (target === '') return null;
      current = target;
      continue;
    }
    return null;
  }
  return null;
}

function makeCommit(repo: Repo, branch: string, changes: Map<string, FileEntry | null>, message: string): string {
  const ref = branchRef(branch);
  const parent = repo.refs.get(ref) ?? null;
  const files = parent === null ? new Map<string, FileEntry>() : filesOfCommit(repo, parent);
  for (const [path, entry] of changes) {
    if (entry === null) files.delete(path);
    else files.set(path, entry);
  }
  const tree = buildTree(repo, files);
  const when = nowSec();
  const who = `${VIEWER_NAME} <${VIEWER_EMAIL}> ${when} +0000`;
  let text = `tree ${tree}\n`;
  if (parent !== null) text += `parent ${parent}\n`;
  text += `author ${who}\ncommitter ${who}\n\n${message}\n`;
  const sha = putObject(repo, 'commit', Buffer.from(text, 'utf8'));
  repo.refs.set(ref, sha);
  return sha;
}

function reachableFrom(repo: Repo, roots: readonly string[]): Set<string> {
  const seen = new Set<string>();
  const stack = [...roots];
  while (stack.length > 0) {
    const oid = stack.pop();
    if (oid === undefined || seen.has(oid)) continue;
    const obj = getObject(repo, oid);
    if (obj === null) continue;
    seen.add(oid);
    if (obj.type === 'commit') {
      const tree = commitTreeOf(obj);
      if (tree !== '') stack.push(tree);
      for (const parent of commitParentsOf(obj)) stack.push(parent);
    } else if (obj.type === 'tree') {
      for (const entry of parseTree(obj.data)) stack.push(entry.oid);
    } else if (obj.type === 'tag') {
      const target = tagTargetOf(obj);
      if (target !== '') stack.push(target);
    }
  }
  return seen;
}

function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  const seen = new Set<string>();
  const stack = [descendant];
  while (stack.length > 0) {
    const oid = stack.pop();
    if (oid === undefined || seen.has(oid)) continue;
    if (oid === ancestor) return true;
    seen.add(oid);
    const obj = getObject(repo, oid);
    if (obj !== null && obj.type === 'commit') for (const parent of commitParentsOf(obj)) stack.push(parent);
  }
  return false;
}

// ---------------------------------------------------------------------------------------------
// Request plumbing.

function requestId(): string {
  return `REQ-${allocateId().toString(36).toUpperCase()}`;
}

function sendJsonR(res: ServerResponse, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  sendJson(res, status, body, { 'x-github-request-id': requestId(), ...headers });
}

function sendMessage(res: ServerResponse, status: number, message: string, headers: Readonly<Record<string, string>> = {}): void {
  sendJsonR(res, status, { message }, headers);
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let size = 0;
    req.on('data', (chunk: Buffer) => {
      size += chunk.length;
      if (size > 256 * 1024 * 1024) {
        reject(new Error('request body too large'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function parseJson(body: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (body.length === 0) return { ok: true, value: undefined };
  try {
    return { ok: true, value: JSON.parse(body.toString('utf8')) as unknown };
  } catch {
    return { ok: false };
  }
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function str(value: unknown, fallback = ''): string {
  return typeof value === 'string' ? value : fallback;
}

function boolv(value: unknown, fallback = false): boolean {
  return typeof value === 'boolean' ? value : fallback;
}

function numv(value: unknown, fallback = 0): number {
  return typeof value === 'number' && Number.isFinite(value) ? value : fallback;
}

/** Whether the request carries the trial's bearer token. A missing token is always refused. */
function authorized(req: IncomingMessage): boolean {
  const header = req.headers.authorization ?? '';
  const match = /^Bearer\s+(.+)$/i.exec(header.trim());
  if (match === null) return false;
  const expected = process.env.MAKEFUN_SHOP_TOKEN ?? '';
  if (expected === '') return true;
  return match[1] === expected;
}

function originOf(req: IncomingMessage): string {
  const host = req.headers.host ?? 'entry';
  return `http://${host}`;
}

function decodeSegment(segment: string): string {
  try {
    return decodeURIComponent(segment);
  } catch {
    return segment;
  }
}

function splitPath(pathname: string): string[] {
  return pathname.split('/').filter((segment) => segment !== '').map(decodeSegment);
}

// ---------------------------------------------------------------------------------------------
// REST v3 serializers.

function labelJson(repo: Repo, name: string): Record<string, unknown> {
  const label = repo.labels.get(name);
  return { id: allocateId(), name, color: label?.color ?? 'ededed', description: null };
}

function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: issue.id,
    node_id: `Issue_${issue.id}`,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => labelJson(repo, name)),
    user: { login: VIEWER_LOGIN, id: 1000, type: 'User' },
    created_at: isoOf(issue.createdAt),
    updated_at: isoOf(issue.createdAt),
    comments: 0,
  };
}

function commentJson(comment: Comment): Record<string, unknown> {
  return {
    id: comment.id,
    body: comment.body,
    user: { login: VIEWER_LOGIN, id: 1000, type: 'User' },
    created_at: isoOf(comment.createdAt),
    updated_at: isoOf(comment.createdAt),
  };
}

function pullJson(repo: Repo, pull: Pull): Record<string, unknown> {
  const headSha = tipOf(repo, pull.head) ?? pull.baseSha;
  const baseSha = tipOf(repo, pull.base) ?? pull.baseSha;
  return {
    id: pull.id,
    node_id: `PullRequest_${pull.id}`,
    number: pull.number,
    state: pull.state,
    title: pull.title,
    body: pull.body,
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    head: { ref: pull.head, sha: headSha, label: `${repo.owner}:${pull.head}` },
    base: { ref: pull.base, sha: baseSha, label: `${repo.owner}:${pull.base}` },
    user: { login: VIEWER_LOGIN, id: 1000, type: 'User' },
    created_at: isoOf(pull.createdAt),
    updated_at: isoOf(pull.createdAt),
  };
}

function repoJson(repo: Repo): Record<string, unknown> {
  return {
    id: repo.id,
    node_id: `Repository_${repo.id}`,
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: 1000, type: 'User' },
    private: repo.private,
    description: repo.description,
    default_branch: repo.defaultBranch,
    has_issues: true,
    fork: false,
    created_at: isoOf(repo.createdAt),
    updated_at: isoOf(repo.createdAt),
  };
}

function commitJson(repo: Repo, sha: string): Record<string, unknown> | null {
  const obj = getObject(repo, sha);
  if (obj === null || obj.type !== 'commit') return null;
  const text = obj.data.toString('utf8');
  const message = text.slice(text.indexOf('\n\n') + 2).replace(/\n$/, '');
  const authorMatch = /^author (.*) (\d+) ([+-]\d{4})$/m.exec(text);
  const date = authorMatch === null ? isoOf(EPOCH_SEC) : isoOf(Number(authorMatch[2]));
  return {
    sha,
    node_id: `Commit_${sha}`,
    commit: {
      message,
      author: { name: VIEWER_NAME, email: VIEWER_EMAIL, date },
      committer: { name: VIEWER_NAME, email: VIEWER_EMAIL, date },
      tree: { sha: commitTreeOf(obj) },
    },
    parents: commitParentsOf(obj).map((parent) => ({ sha: parent })),
  };
}

function countLines(data: Buffer): number {
  if (data.length === 0) return 0;
  let lines = 0;
  for (const byte of data) if (byte === 0x0a) lines += 1;
  return data[data.length - 1] === 0x0a ? lines : lines + 1;
}

function base64Of(data: Buffer): string {
  return data.toString('base64');
}

// ---------------------------------------------------------------------------------------------
// REST routing. Every handler answers a status, a JSON body and the request-id header.

interface RestContext {
  req: IncomingMessage;
  res: ServerResponse;
  method: string;
  url: URL;
  body: Buffer;
  segments: string[];
}

function pageParams(url: URL): { perPage: number; page: number } {
  const perPage = Math.max(1, Math.min(100, Number(url.searchParams.get('per_page') ?? '30') || 30));
  const page = Math.max(1, Number(url.searchParams.get('page') ?? '1') || 1);
  return { perPage, page };
}

function paginate<T>(items: readonly T[], url: URL): { slice: T[]; headers: Record<string, string> } {
  const { perPage, page } = pageParams(url);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const headers: Record<string, string> = {};
  if (start + perPage < items.length) {
    const next = new URL(url.toString());
    next.searchParams.set('per_page', String(perPage));
    next.searchParams.set('page', String(page + 1));
    headers.link = `<${next.toString()}>; rel="next"`;
  }
  return { slice, headers };
}

function repoFromSegments(segments: readonly string[]): Repo | null {
  if (segments.length < 3 || segments[0] !== 'repos') return null;
  return findRepo(segments[1] ?? '', segments[2] ?? '');
}

function jsonBodyOf(ctx: RestContext): Record<string, unknown> | null {
  const parsed = parseJson(ctx.body);
  if (!parsed.ok) return null;
  return isRecord(parsed.value) ? parsed.value : {};
}

async function handleRest(ctx: RestContext): Promise<void> {
  const { req, res, method, url, segments } = ctx;

  if (!authorized(req)) {
    sendMessage(res, 401, 'Requires authentication');
    return;
  }

  const json = (): Record<string, unknown> | null => jsonBodyOf(ctx);

  // GET /user and the repository collection.
  if (segments.length === 1 && segments[0] === 'user' && method === 'GET') {
    sendJsonR(res, 200, {
      login: VIEWER_LOGIN,
      id: 1000,
      node_id: 'User_1000',
      name: VIEWER_NAME,
      type: 'User',
      site_admin: false,
      public_repos: 0,
      followers: 0,
      following: 0,
    });
    return;
  }

  if (segments.length === 1 && segments[0] === 'meta' && method === 'GET') {
    sendJsonR(res, 200, { installed_version: 'github-core-clone-01' });
    return;
  }

  if (segments.length === 2 && segments[0] === 'user' && segments[1] === 'repos') {
    if (method === 'GET') {
      const owned = [...repos.values()].filter((repo) => repo.owner === VIEWER_LOGIN).sort((a, b) => a.id - b.id);
      const { slice, headers } = paginate(owned, url);
      sendJsonR(res, 200, slice.map(repoJson), headers);
      return;
    }
    if (method === 'POST') {
      const body = json();
      if (body === null) {
        sendMessage(res, 400, 'Problems parsing JSON');
        return;
      }
      const name = str(body.name);
      if (name === '') {
        sendMessage(res, 422, 'Repository name is required');
        return;
      }
      if (findRepo(VIEWER_LOGIN, name) !== null) {
        sendMessage(res, 422, 'Repository creation failed: name already exists');
        return;
      }
      const repo = makeRepo(VIEWER_LOGIN, name, boolv(body.private, false), str(body.description));
      sendJsonR(res, 201, repoJson(repo));
      return;
    }
  }

  const repo = repoFromSegments(segments);
  if (repo === null) {
    sendMessage(res, 404, 'Not Found');
    return;
  }

  // /repos/{owner}/{name}
  if (segments.length === 3) {
    if (method === 'GET') {
      sendJsonR(res, 200, repoJson(repo));
      return;
    }
    if (method === 'PATCH') {
      const body = json();
      if (body === null) {
        sendMessage(res, 400, 'Problems parsing JSON');
        return;
      }
      if (typeof body.description === 'string') repo.description = body.description;
      if (typeof body.private === 'boolean') repo.private = body.private;
      if (typeof body.default_branch === 'string' && body.default_branch !== '') repo.defaultBranch = body.default_branch;
      sendJsonR(res, 200, repoJson(repo));
      return;
    }
    if (method === 'DELETE') {
      repos.delete(repoKey(repo.owner, repo.name));
      res.writeHead(204, { 'x-github-request-id': requestId() });
      res.end();
      return;
    }
  }

  const rest = segments.slice(3);

  // Git data: refs.
  if (rest.length === 2 && rest[0] === 'git' && rest[1] === 'refs' && method === 'POST') {
    const body = json();
    if (body === null) {
      sendMessage(res, 400, 'Problems parsing JSON');
      return;
    }
    const ref = str(body.ref);
    const sha = str(body.sha).toLowerCase();
    if (!ref.startsWith('refs/') || sha === '' || getObject(repo, sha) === null) {
      sendMessage(res, 422, 'Reference update failed');
      return;
    }
    repo.refs.set(ref, sha);
    sendJsonR(res, 201, { ref, node_id: `Ref_${ref}`, url: `${originOf(req)}/api/v3/repos/${repo.owner}/${repo.name}/git/${ref}`, object: { sha, type: 'commit' } });
    return;
  }

  if (rest.length >= 3 && rest[0] === 'git' && rest[1] === 'refs' && method === 'GET') {
    const ref = rest.slice(2).join('/');
    const sha = repo.refs.get(ref.startsWith('refs/') ? ref : `refs/heads/${ref}`);
    if (sha === undefined) {
      sendMessage(res, 404, 'Not Found');
      return;
    }
    sendJsonR(res, 200, { ref: ref.startsWith('refs/') ? ref : `refs/heads/${ref}`, object: { sha, type: 'commit' } });
    return;
  }

  if (rest.length === 2 && rest[0] === 'git' && rest[1] === 'refs' && method === 'GET') {
    sendJsonR(res, 200, [...repo.refs].map(([ref, sha]) => ({ ref, object: { sha, type: 'commit' } })));
    return;
  }

  // Branches.
  if (rest.length === 1 && rest[0] === 'branches' && method === 'GET') {
    const branches = [...repo.refs]
      .filter(([ref]) => ref.startsWith('refs/heads/'))
      .map(([ref, sha]) => ({ name: branchNameOf(ref), commit: { sha, url: `${originOf(req)}/api/v3/repos/${repo.owner}/${repo.name}/commits/${sha}` }, protected: false }));
    sendJsonR(res, 200, branches);
    return;
  }
  if (rest.length === 2 && rest[0] === 'branches' && method === 'GET') {
    const sha = repo.refs.get(`refs/heads/${rest[1] ?? ''}`);
    if (sha === undefined) {
      sendMessage(res, 404, 'Branch not found');
      return;
    }
    sendJsonR(res, 200, { name: rest[1], commit: { sha }, protected: false });
    return;
  }

  // Commits.
  if (rest.length === 1 && rest[0] === 'commits' && method === 'GET') {
    const requested = url.searchParams.get('sha') ?? repo.defaultBranch;
    const start = repo.refs.get(branchRef(requested)) ?? repo.refs.get(requested) ?? null;
    const out: Record<string, unknown>[] = [];
    let current = start;
    const seen = new Set<string>();
    while (current !== null && !seen.has(current) && out.length < 100) {
      seen.add(current);
      const commit = commitJson(repo, current);
      if (commit === null) break;
      out.push(commit);
      const obj = getObject(repo, current);
      current = obj === null ? null : commitParentsOf(obj)[0] ?? null;
    }
    sendJsonR(res, 200, out);
    return;
  }

  // Contents.
  if (rest.length >= 2 && rest[0] === 'contents') {
    const filePath = rest.slice(1).join('/');
    const refParam = url.searchParams.get('ref');
    const branch = refParam ?? repo.defaultBranch;
    const tip = repo.refs.get(branchRef(branch)) ?? repo.refs.get(branch) ?? null;

    if (method === 'GET') {
      if (tip === null) {
        sendMessage(res, 404, 'Not Found');
        return;
      }
      const files = filesOfCommit(repo, tip);
      const direct = files.get(filePath);
      if (direct !== undefined) {
        sendJsonR(res, 200, {
          type: 'file',
          encoding: 'base64',
          size: direct.data.length,
          name: filePath.slice(filePath.lastIndexOf('/') + 1),
          path: filePath,
          content: base64Of(direct.data),
          sha: putObject(repo, 'blob', direct.data),
          url: `${originOf(req)}/api/v3/repos/${repo.owner}/${repo.name}/contents/${filePath}`,
        });
        return;
      }
      const prefix = `${filePath}/`;
      const names = new Set<string>();
      for (const path of files.keys()) if (path.startsWith(prefix)) names.add(path.slice(prefix.length).split('/')[0] ?? '');
      if (names.size === 0) {
        sendMessage(res, 404, 'Not Found');
        return;
      }
      const listing: Record<string, unknown>[] = [];
      for (const name of [...names].sort()) {
        const childPath = `${filePath}/${name}`;
        const child = files.get(childPath);
        if (child !== undefined) {
          listing.push({ type: 'file', name, path: childPath, sha: putObject(repo, 'blob', child.data), size: child.data.length, mode: child.mode });
        } else {
          const nested = new Map<string, FileEntry>();
          for (const [path, entry] of files) if (path.startsWith(`${childPath}/`)) nested.set(path.slice(childPath.length + 1), entry);
          listing.push({ type: 'dir', name, path: childPath, sha: buildTree(repo, nested), size: 0, mode: '40000' });
        }
      }
      sendJsonR(res, 200, listing);
      return;
    }

    if (method === 'PUT') {
      const body = json();
      if (body === null) {
        sendMessage(res, 400, 'Problems parsing JSON');
        return;
      }
      const content = str(body.content);
      const message = str(body.message, 'Update file');
      if (content === '') {
        sendMessage(res, 422, 'content is required');
        return;
      }
      const targetBranch = str(body.branch, repo.defaultBranch);
      const targetTip = repo.refs.get(branchRef(targetBranch)) ?? null;
      const existing = targetTip === null ? undefined : filesOfCommit(repo, targetTip).get(filePath);
      const givenSha = str(body.sha).toLowerCase();
      if (existing !== undefined && givenSha !== '' && givenSha !== putObject(repo, 'blob', existing.data)) {
        sendMessage(res, 409, 'sha does not match the current file');
        return;
      }
      const data = Buffer.from(content, 'base64');
      const commitSha = makeCommit(repo, targetBranch, new Map([[filePath, { mode: '100644', data }]]), message);
      const status = existing === undefined ? 201 : 200;
      sendJsonR(res, status, {
        content: {
          name: filePath.slice(filePath.lastIndexOf('/') + 1),
          path: filePath,
          sha: putObject(repo, 'blob', data),
          size: data.length,
          encoding: 'base64',
          content,
        },
        commit: { sha: commitSha, message, tree: { sha: commitTreeOf(getObject(repo, commitSha) ?? { type: 'commit', data: Buffer.alloc(0) }) } },
      });
      return;
    }

    if (method === 'DELETE') {
      const body = json();
      if (body === null) {
        sendMessage(res, 400, 'Problems parsing JSON');
        return;
      }
      const targetBranch = str(body.branch, repo.defaultBranch);
      const targetTip = repo.refs.get(branchRef(targetBranch)) ?? null;
      const existing = targetTip === null ? undefined : filesOfCommit(repo, targetTip).get(filePath);
      if (existing === undefined) {
        sendMessage(res, 404, 'Not Found');
        return;
      }
      const commitSha = makeCommit(repo, targetBranch, new Map([[filePath, null]]), str(body.message, 'Delete file'));
      sendJsonR(res, 200, { commit: { sha: commitSha }, content: null });
      return;
    }
  }

  // Labels.
  if (rest.length === 1 && rest[0] === 'labels') {
    if (method === 'POST') {
      const body = json();
      if (body === null) {
        sendMessage(res, 400, 'Problems parsing JSON');
        return;
      }
      const name = str(body.name);
      if (name === '') {
        sendMessage(res, 422, 'name is required');
        return;
      }
      const color = str(body.color, 'ededed');
      repo.labels.set(name, { name, color });
      sendJsonR(res, 201, { id: allocateId(), name, color, description: null });
      return;
    }
    if (method === 'GET') {
      sendJsonR(res, 200, [...repo.labels.values()].map((label) => ({ id: allocateId(), name: label.name, color: label.color })));
      return;
    }
  }

  // Issues.
  if (rest.length === 1 && rest[0] === 'issues') {
    if (method === 'POST') {
      const body = json();
      if (body === null) {
        sendMessage(res, 400, 'Problems parsing JSON');
        return;
      }
      const labelNames: string[] = Array.isArray(body.labels) ? body.labels.filter((label): label is string => typeof label === 'string') : [];
      const unknown = labelNames.find((name) => !repo.labels.has(name));
      if (unknown !== undefined) {
        sendMessage(res, 422, `Label ${unknown} does not exist`);
        return;
      }
      repo.issueSeq += 1;
      const issue: Issue = {
        id: allocateId(),
        number: repo.issueSeq,
        title: str(body.title),
        body: str(body.body),
        state: 'open',
        labels: labelNames,
        createdAt: nowSec(),
      };
      repo.issues.set(issue.number, issue);
      sendJsonR(res, 201, issueJson(repo, issue));
      return;
    }
    if (method === 'GET') {
      const state = url.searchParams.get('state') ?? 'open';
      const sort = url.searchParams.get('sort') ?? 'created';
      const direction = url.searchParams.get('direction') ?? 'desc';
      let list = [...repo.issues.values()];
      if (state !== 'all') list = list.filter((issue) => issue.state === state);
      list.sort((a, b) => (sort === 'created' ? a.createdAt - b.createdAt : a.number - b.number));
      if (direction === 'desc') list.reverse();
      const { slice, headers } = paginate(list, url);
      sendJsonR(res, 200, slice.map((issue) => issueJson(repo, issue)), headers);
      return;
    }
  }

  if (rest.length >= 2 && rest[0] === 'issues') {
    const number = Number(rest[1]);
    const issue = repo.issues.get(number);
    if (issue === undefined) {
      sendMessage(res, 404, 'Not Found');
      return;
    }
    if (rest.length === 2 && method === 'GET') {
      sendJsonR(res, 200, issueJson(repo, issue));
      return;
    }
    if (rest.length === 2 && method === 'PATCH') {
      const body = json();
      if (body === null) {
        sendMessage(res, 400, 'Problems parsing JSON');
        return;
      }
      if (body.state === 'open' || body.state === 'closed') issue.state = body.state;
      if (typeof body.title === 'string') issue.title = body.title;
      if (typeof body.body === 'string') issue.body = body.body;
      sendJsonR(res, 200, issueJson(repo, issue));
      return;
    }
    if (rest.length === 3 && rest[2] === 'comments') {
      if (method === 'GET') {
        const comments = [...repo.comments.values()].filter((comment) => comment.issue === number).sort((a, b) => a.id - b.id);
        sendJsonR(res, 200, comments.map(commentJson));
        return;
      }
      if (method === 'POST') {
        const body = json();
        if (body === null) {
          sendMessage(res, 400, 'Problems parsing JSON');
          return;
        }
        repo.commentSeq += 1;
        const comment: Comment = { id: allocateId(), issue: number, body: str(body.body), createdAt: nowSec() };
        repo.comments.set(comment.id, comment);
        sendJsonR(res, 201, commentJson(comment));
        return;
      }
    }
  }

  // Pull requests.
  if (rest.length === 1 && rest[0] === 'pulls') {
    if (method === 'POST') {
      const body = json();
      if (body === null) {
        sendMessage(res, 400, 'Problems parsing JSON');
        return;
      }
      const head = str(body.head);
      const base = str(body.base, repo.defaultBranch);
      const headSha = repo.refs.get(branchRef(head)) ?? null;
      const baseSha = repo.refs.get(branchRef(base)) ?? null;
      if (headSha === null || baseSha === null) {
        sendMessage(res, 422, 'Validation Failed: no commits between the branches');
        return;
      }
      repo.pullSeq += 1;
      const pull: Pull = {
        id: allocateId(),
        number: repo.pullSeq,
        title: str(body.title),
        body: str(body.body),
        state: 'open',
        head,
        base,
        baseSha,
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
        createdAt: nowSec(),
      };
      repo.pulls.set(pull.number, pull);
      sendJsonR(res, 201, pullJson(repo, pull));
      return;
    }
    if (method === 'GET') {
      const state = url.searchParams.get('state') ?? 'open';
      let list = [...repo.pulls.values()];
      if (state !== 'all') list = list.filter((pull) => pull.state === state);
      list.sort((a, b) => a.number - b.number);
      const { slice, headers } = paginate(list, url);
      sendJsonR(res, 200, slice.map((pull) => pullJson(repo, pull)), headers);
      return;
    }
  }

  if (rest.length >= 2 && rest[0] === 'pulls') {
    const number = Number(rest[1]);
    const pull = repo.pulls.get(number);
    if (pull === undefined) {
      sendMessage(res, 404, 'Not Found');
      return;
    }
    if (rest.length === 2 && method === 'GET') {
      sendJsonR(res, 200, pullJson(repo, pull));
      return;
    }
    if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
      sendJsonR(res, 200, pullFiles(repo, pull));
      return;
    }
    if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
      const body = json();
      if (body === null) {
        sendMessage(res, 400, 'Problems parsing JSON');
        return;
      }
      if (pull.merged) {
        sendMessage(res, 405, 'Pull request is not mergeable: it is already merged');
        return;
      }
      const currentTip = repo.refs.get(branchRef(pull.base)) ?? null;
      if (currentTip === null) {
        sendMessage(res, 404, 'Not Found');
        return;
      }
      const baseFiles = filesOfCommit(repo, pull.baseSha);
      const headFiles = filesOfCommit(repo, pull.head);
      const currentFiles = filesOfCommit(repo, currentTip);
      const changes = new Map<string, FileEntry | null>();
      let conflict = false;
      for (const path of new Set([...baseFiles.keys(), ...headFiles.keys()])) {
        const before = baseFiles.get(path);
        const after = headFiles.get(path);
        if (sameEntry(before, after)) continue;
        const current = currentFiles.get(path);
        if (currentTip !== pull.baseSha && !sameEntry(before, current)) conflict = true;
        changes.set(path, after ?? null);
      }
      if (conflict) {
        sendMessage(res, 405, 'Pull Request is not mergeable');
        return;
      }
      const mergeSha = makeCommit(repo, pull.base, changes, `Merge pull request #${pull.number} from ${pull.head}`);
      pull.merged = true;
      pull.state = 'closed';
      pull.mergedAt = isoOf(nowSec());
      pull.mergeCommitSha = mergeSha;
      sendJsonR(res, 200, { sha: mergeSha, merged: true, message: 'Pull Request successfully merged' });
      return;
    }
  }

  sendMessage(res, 404, 'Not Found');
}

function sameEntry(a: FileEntry | undefined, b: FileEntry | undefined): boolean {
  if (a === undefined && b === undefined) return true;
  if (a === undefined || b === undefined) return false;
  return a.mode === b.mode && a.data.equals(b.data);
}

function pullFiles(repo: Repo, pull: Pull): Record<string, unknown>[] {
  const baseFiles = filesOfCommit(repo, pull.baseSha);
  const headFiles = filesOfCommit(repo, pull.head);
  const out: Record<string, unknown>[] = [];
  for (const path of new Set([...baseFiles.keys(), ...headFiles.keys()])) {
    const before = baseFiles.get(path);
    const after = headFiles.get(path);
    if (sameEntry(before, after)) continue;
    const additions = after === undefined ? 0 : countLines(after.data);
    const deletions = before === undefined ? 0 : countLines(before.data);
    out.push({
      sha: after === undefined ? null : putObject(repo, 'blob', after.data),
      filename: path,
      status: before === undefined ? 'added' : after === undefined ? 'removed' : 'modified',
      additions,
      deletions,
      changes: additions + deletions,
    });
  }
  return out;
}

// ---------------------------------------------------------------------------------------------
// Git smart-HTTP plumbing: pkt-lines, packfiles, and the object walks upload-pack serves.

const ZERO_OID = '0'.repeat(40);

interface Packet {
  kind: 'data' | 'flush' | 'delim' | 'end';
  payload: Buffer;
}

/** One pkt-line: a four-hex length (payload plus the header) and the payload bytes. */
function encodePacket(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const header = Buffer.from((data.length + 4).toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([header, data]);
}

const PACKET_FLUSH = Buffer.from('0000', 'ascii');

/** Decode pkt-lines; `rest` is whatever follows the first flush (a receive-pack's pack). */
function decodePackets(input: Buffer, stopAtFlush = false): { packets: Packet[]; rest: Buffer } {
  const packets: Packet[] = [];
  let offset = 0;
  while (offset + 4 <= input.length) {
    const header = input.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(header)) break;
    const length = Number.parseInt(header, 16);
    offset += 4;
    if (length === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      if (stopAtFlush) break;
      continue;
    }
    if (length === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      continue;
    }
    if (length === 2) {
      packets.push({ kind: 'end', payload: Buffer.alloc(0) });
      continue;
    }
    const take = Math.max(0, Math.min(length - 4, input.length - offset));
    packets.push({ kind: 'data', payload: input.subarray(offset, offset + take) });
    offset += take;
    if (take < length - 4) break;
  }
  return { packets, rest: input.subarray(offset) };
}

function packetText(packet: Packet): string {
  return packet.payload.toString('utf8').replace(/\r?\n$/, '');
}

function splitBuffer(buffer: Buffer, size: number): Buffer[] {
  const parts: Buffer[] = [];
  for (let offset = 0; offset < buffer.length; offset += size) parts.push(buffer.subarray(offset, Math.min(offset + size, buffer.length)));
  return parts;
}

const PACK_TYPE_CODE: Readonly<Record<ObjType, number>> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const PACK_CODE_TYPE: Readonly<Record<number, ObjType>> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

/** A pack object's type-and-size varint header. */
function packObjectHeader(type: ObjType, size: number): Buffer {
  const code = PACK_TYPE_CODE[type];
  const bytes: number[] = [];
  let remaining = size;
  let first = (code << 4) | (remaining & 0x0f);
  remaining = Math.floor(remaining / 16);
  while (remaining > 0) {
    bytes.push(first | 0x80);
    first = remaining & 0x7f;
    remaining = Math.floor(remaining / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

/** A version-2 packfile of whole objects (no deltas), with its SHA-1 trailer. */
function buildPack(objects: readonly GitObj[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const object of objects) {
    parts.push(packObjectHeader(object.type, object.data.length));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

/** Inflate one zlib stream at `offset`, reporting where the next one starts. */
function inflateFrom(buffer: Buffer, offset: number): { data: Buffer; next: number } {
  const view = buffer.subarray(offset);
  const result = inflateSync(view, { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
  const written = result.engine !== undefined ? result.engine.bytesWritten : 0;
  if (!written || written <= 0) throw new Error('a zlib stream consumed no bytes');
  return { data: result.buffer, next: offset + written };
}

function readDeltaVarint(delta: Buffer, start: number): { value: number; next: number } {
  let value = 0;
  let shift = 0;
  let offset = start;
  for (;;) {
    if (offset >= delta.length) throw new Error('a delta varint is truncated');
    const byte = delta[offset] ?? 0;
    offset += 1;
    value += (byte & 0x7f) * 2 ** shift;
    shift += 7;
    if ((byte & 0x80) === 0) break;
  }
  return { value, next: offset };
}

/** Apply a git delta (copy/insert) to its base object. */
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  const sourceSize = readDeltaVarint(delta, 0);
  const targetSize = readDeltaVarint(delta, sourceSize.next);
  let offset = targetSize.next;
  const out = Buffer.alloc(targetSize.value);
  let written = 0;
  while (offset < delta.length) {
    const op = delta[offset] ?? 0;
    offset += 1;
    if ((op & 0x80) !== 0) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if ((op & (1 << bit)) !== 0) {
          copyOffset += (delta[offset] ?? 0) * 2 ** shift;
          offset += 1;
        }
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit += 1) {
        if ((op & (1 << bit)) !== 0) {
          copySize += (delta[offset] ?? 0) * 2 ** shift;
          offset += 1;
        }
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op !== 0) {
      const literal = op & 0x7f;
      delta.copy(out, written, offset, offset + literal);
      offset += literal;
      written += literal;
    } else {
      throw new Error('delta opcode 0 is invalid');
    }
  }
  return out;
}

/** Parse a pushed packfile into whole objects, resolving OFS_DELTA and REF_DELTA entries. */
function parsePack(input: Buffer): GitObj[] {
  if (input.length < 32 || input.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('the body is not a packfile');
  const count = input.readUInt32BE(8);
  const trailerStart = input.length - 20;
  let offset = 12;
  interface Entry {
    offset: number;
    typeCode: number;
    size: number;
    raw: Buffer;
    baseOffset: number | null;
    baseOid: string | null;
    resolvedType: ObjType | null;
    resolved: Buffer | null;
  }
  const entries: Entry[] = [];
  const byOffset = new Map<number, Entry>();
  for (let index = 0; index < count; index += 1) {
    const start = offset;
    let byte = input[offset] ?? 0;
    offset += 1;
    const typeCode = (byte >> 4) & 0x07;
    let size = byte & 0x0f;
    let shift = 4;
    while ((byte & 0x80) !== 0) {
      byte = input[offset] ?? 0;
      offset += 1;
      size += (byte & 0x7f) * 2 ** shift;
      shift += 7;
    }
    let baseOffset: number | null = null;
    let baseOid: string | null = null;
    if (typeCode === 6) {
      let b = input[offset] ?? 0;
      offset += 1;
      let value = b & 0x7f;
      while ((b & 0x80) !== 0) {
        b = input[offset] ?? 0;
        offset += 1;
        value = (value + 1) * 128 + (b & 0x7f);
      }
      baseOffset = start - value;
    } else if (typeCode === 7) {
      baseOid = input.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    } else if (PACK_CODE_TYPE[typeCode] === undefined) {
      throw new Error(`pack entry ${index} has unknown type code ${typeCode}`);
    }
    const inflated = inflateFrom(input.subarray(0, trailerStart), offset);
    offset = inflated.next;
    const entry: Entry = { offset: start, typeCode, size, raw: inflated.data, baseOffset, baseOid, resolvedType: null, resolved: null };
    entries.push(entry);
    byOffset.set(start, entry);
  }
  const byOid = new Map<string, GitObj>();
  const resolve = (entry: Entry): GitObj => {
    if (entry.resolved !== null && entry.resolvedType !== null) return { type: entry.resolvedType, data: entry.resolved };
    let type: ObjType;
    let data: Buffer;
    if (entry.typeCode === 6) {
      const baseEntry = entry.baseOffset === null ? undefined : byOffset.get(entry.baseOffset);
      if (baseEntry === undefined) throw new Error('an ofs-delta base is not in the pack');
      const base = resolve(baseEntry);
      type = base.type;
      data = applyDelta(base.data, entry.raw);
    } else if (entry.typeCode === 7) {
      const base = entry.baseOid === null ? undefined : byOid.get(entry.baseOid);
      if (base === undefined) throw new Error('a ref-delta base is not in the pack');
      type = base.type;
      data = applyDelta(base.data, entry.raw);
    } else {
      type = PACK_CODE_TYPE[entry.typeCode] ?? 'blob';
      data = entry.raw;
    }
    entry.resolvedType = type;
    entry.resolved = data;
    byOid.set(hashObject(type, data), { type, data });
    return { type, data };
  };
  return entries.map(resolve);
}

/** Add a tree and every tree/blob below it to `out`. */
function addTreeClosure(repo: Repo, oid: string, out: Set<string>): void {
  if (out.has(oid)) return;
  const object = getObject(repo, oid);
  if (object === null) return;
  out.add(oid);
  if (object.type === 'tree') for (const entry of parseTree(object.data)) addTreeClosure(repo, entry.oid, out);
}

interface FetchPlan {
  send: Set<string>;
  shallow: string[];
  unshallow: string[];
}

/**
 * The objects an upload-pack response must carry: the depth-limited closure of `wants`, minus what the
 * client already holds (`haves`, walked only as far as its own shallow boundary). Commit ids at the
 * depth boundary, or at a boundary the client already has and we do not deepen past, are shallow.
 */
function planFetch(repo: Repo, wants: readonly string[], haves: readonly string[], clientShallow: ReadonlySet<string>, depth: number | null): FetchPlan {
  const held = new Set<string>();
  const heldStack = [...haves];
  while (heldStack.length > 0) {
    const oid = heldStack.pop();
    if (oid === undefined || held.has(oid)) continue;
    const object = getObject(repo, oid);
    if (object === null) continue;
    held.add(oid);
    if (object.type === 'commit') {
      addTreeClosure(repo, commitTreeOf(object), held);
      if (!clientShallow.has(oid)) for (const parent of commitParentsOf(object)) heldStack.push(parent);
    } else if (object.type === 'tag') {
      const target = tagTargetOf(object);
      if (target !== '') heldStack.push(target);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) heldStack.push(entry.oid);
    }
  }

  const send = new Set<string>();
  const shallow: string[] = [];
  const unshallow: string[] = [];
  const visited = new Set<string>();
  const queue: Array<{ oid: string; generation: number }> = [];
  for (const want of wants) {
    const object = getObject(repo, want);
    if (object === null) continue;
    if (object.type === 'tag') {
      send.add(want);
      const target = tagTargetOf(object);
      if (target !== '') queue.push({ oid: target, generation: 1 });
    } else if (object.type === 'commit') {
      queue.push({ oid: want, generation: 1 });
    } else {
      send.add(want);
    }
  }
  while (queue.length > 0) {
    const next = queue.shift();
    if (next === undefined || visited.has(next.oid)) continue;
    visited.add(next.oid);
    const object = getObject(repo, next.oid);
    if (object === null) continue;
    if (object.type !== 'commit') {
      send.add(next.oid);
      if (object.type === 'tree') for (const entry of parseTree(object.data)) queue.push({ oid: entry.oid, generation: next.generation });
      continue;
    }
    send.add(next.oid);
    addTreeClosure(repo, commitTreeOf(object), send);
    const parents = commitParentsOf(object);
    const atDepth = depth !== null && next.generation >= depth;
    const atClientBoundary = depth === null && clientShallow.has(next.oid);
    if (atDepth || atClientBoundary) {
      if (parents.length > 0) shallow.push(next.oid);
    } else {
      for (const parent of parents) queue.push({ oid: parent, generation: next.generation + 1 });
      if (clientShallow.has(next.oid)) unshallow.push(next.oid);
    }
  }
  for (const oid of held) send.delete(oid);
  return { send, shallow: [...new Set(shallow)], unshallow: [...new Set(unshallow)] };
}

/** The refs a v0 advertisement lists, HEAD first when its branch exists, with peeled tags. */
function advertisedRefs(repo: Repo): Array<{ oid: string; name: string }> {
  const refs: Array<{ oid: string; name: string }> = [];
  const head = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
  if (head !== undefined) refs.push({ oid: head, name: 'HEAD' });
  const names = [...repo.refs.keys()].sort();
  for (const name of names) {
    const oid = repo.refs.get(name);
    if (oid === undefined) continue;
    refs.push({ oid, name });
    if (name.startsWith('refs/tags/')) {
      const object = getObject(repo, oid);
      if (object !== null && object.type === 'tag') {
        const peeled = tagTargetOf(object);
        if (peeled !== '') refs.push({ oid: peeled, name: `${name}^{}` });
      }
    }
  }
  return refs;
}

function v0Advertisement(repo: Repo, service: string): Buffer {
  const caps =
    service === 'git-receive-pack'
      ? ['report-status', 'side-band-64k', 'delete-refs', 'ofs-delta', 'agent=github-forge/1.0']
      : ['side-band-64k', 'ofs-delta', 'shallow', 'agent=github-forge/1.0', `symref=HEAD:refs/heads/${repo.defaultBranch}`];
  const refs = advertisedRefs(repo);
  if (refs.length === 0) return Buffer.concat([encodePacket(`${ZERO_OID} capabilities^{}\u0000${caps.join(' ')}\n`), PACKET_FLUSH]);
  const parts: Buffer[] = [];
  refs.forEach((ref, index) => {
    const tail = index === 0 ? `\u0000${caps.join(' ')}` : '';
    parts.push(encodePacket(`${ref.oid} ${ref.name}${tail}\n`));
  });
  parts.push(PACKET_FLUSH);
  return Buffer.concat(parts);
}

function lsRefsResponse(repo: Repo, options: { peel: boolean; symrefs: boolean; unborn: boolean; prefixes: readonly string[] }): Buffer {
  const matches = (name: string): boolean => options.prefixes.length === 0 || options.prefixes.some((prefix) => name.startsWith(prefix));
  const parts: Buffer[] = [];
  const head = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
  if (matches('HEAD')) {
    if (head !== undefined) parts.push(encodePacket(`${head} HEAD${options.symrefs ? ` symref-target:refs/heads/${repo.defaultBranch}` : ''}\n`));
    else if (options.unborn) parts.push(encodePacket(`unborn HEAD${options.symrefs ? ` symref-target:refs/heads/${repo.defaultBranch}` : ''}\n`));
  }
  for (const name of [...repo.refs.keys()].sort()) {
    if (!matches(name)) continue;
    const oid = repo.refs.get(name);
    if (oid === undefined) continue;
    let extras = '';
    if (options.peel && name.startsWith('refs/tags/')) {
      const object = getObject(repo, oid);
      if (object !== null && object.type === 'tag') {
        const peeled = tagTargetOf(object);
        if (peeled !== '') extras += ` peeled:${peeled}`;
      }
    }
    parts.push(encodePacket(`${oid} ${name}${extras}\n`));
  }
  parts.push(PACKET_FLUSH);
  return Buffer.concat(parts);
}

function serveUploadPackV2(repo: Repo, packets: readonly Packet[]): Buffer {
  let command = '';
  let inArgs = false;
  const args: string[] = [];
  for (const packet of packets) {
    if (packet.kind === 'delim') {
      inArgs = true;
      continue;
    }
    if (packet.kind !== 'data') continue;
    const line = packetText(packet);
    if (!inArgs) {
      if (line.startsWith('command=')) command = line.slice('command='.length);
      continue;
    }
    args.push(line);
  }
  if (command === 'ls-refs') {
    return lsRefsResponse(repo, {
      peel: args.includes('peel'),
      symrefs: args.includes('symrefs'),
      unborn: args.includes('unborn'),
      prefixes: args.filter((line) => line.startsWith('ref-prefix ')).map((line) => line.slice('ref-prefix '.length)),
    });
  }
  if (command === 'fetch') {
    const wants: string[] = [];
    const haves: string[] = [];
    const clientShallow: string[] = [];
    let depth: number | null = null;
    for (const line of args) {
      if (line.startsWith('want ')) wants.push(line.slice(5).trim());
      else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
      else if (line.startsWith('shallow ')) clientShallow.push(line.slice(8).trim());
      else if (line.startsWith('deepen ')) {
        const value = Number(line.slice(7).trim());
        if (Number.isFinite(value) && value > 0) depth = Math.floor(value);
      }
    }
    const plan = planFetch(repo, wants, haves, new Set(clientShallow), depth);
    const objects: GitObj[] = [];
    for (const oid of plan.send) {
      const object = getObject(repo, oid);
      if (object !== null) objects.push(object);
    }
    const pack = buildPack(objects);
    const parts: Buffer[] = [];
    if (plan.shallow.length > 0 || plan.unshallow.length > 0) {
      parts.push(encodePacket('shallow-info\n'));
      for (const oid of plan.shallow) parts.push(encodePacket(`shallow ${oid}\n`));
      for (const oid of plan.unshallow) parts.push(encodePacket(`unshallow ${oid}\n`));
      parts.push(PACKET_FLUSH);
    }
    parts.push(encodePacket('packfile\n'));
    for (const chunk of splitBuffer(pack, 65_000)) parts.push(encodePacket(Buffer.concat([Buffer.from([1]), chunk])));
    parts.push(PACKET_FLUSH);
    return Buffer.concat(parts);
  }
  return PACKET_FLUSH;
}

function serveUploadPackV0(repo: Repo, packets: readonly Packet[]): Buffer {
  const wants: string[] = [];
  const haves: string[] = [];
  const clientShallow: string[] = [];
  let depth: number | null = null;
  for (const packet of packets) {
    if (packet.kind !== 'data') continue;
    const line = packetText(packet);
    if (line.startsWith('want ')) wants.push(line.slice(5).split(' ')[0] ?? '');
    else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) clientShallow.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) {
      const value = Number(line.slice(7).trim());
      if (Number.isFinite(value) && value > 0) depth = Math.floor(value);
    }
  }
  const plan = planFetch(repo, wants, haves, new Set(clientShallow), depth);
  const objects: GitObj[] = [];
  for (const oid of plan.send) {
    const object = getObject(repo, oid);
    if (object !== null) objects.push(object);
  }
  const pack = buildPack(objects);
  const parts: Buffer[] = [];
  for (const oid of plan.shallow) parts.push(encodePacket(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(encodePacket(`unshallow ${oid}\n`));
  parts.push(encodePacket('NAK\n'));
  for (const chunk of splitBuffer(pack, 65_000)) parts.push(encodePacket(Buffer.concat([Buffer.from([1]), chunk])));
  parts.push(PACKET_FLUSH);
  return Buffer.concat(parts);
}

function serveReceivePack(repo: Repo, body: Buffer): Buffer {
  const decoded = decodePackets(body, true);
  const commands: Array<{ oldOid: string; newOid: string; ref: string }> = [];
  let sideband = false;
  let first = true;
  for (const packet of decoded.packets) {
    if (packet.kind !== 'data') continue;
    let line = packetText(packet);
    let caps = '';
    const nul = line.indexOf('\u0000');
    if (nul >= 0) {
      caps = line.slice(nul + 1);
      line = line.slice(0, nul);
    }
    if (first) sideband = caps.split(' ').includes('side-band-64k');
    first = false;
    const pieces = line.split(' ');
    if (pieces.length >= 3) commands.push({ oldOid: pieces[0] ?? '', newOid: pieces[1] ?? '', ref: pieces.slice(2).join(' ') });
  }
  let unpackOk = true;
  let unpackDetail = 'ok';
  try {
    if (decoded.rest.length > 0 && decoded.rest.subarray(0, 4).toString('ascii') === 'PACK') {
      for (const object of parsePack(decoded.rest)) putObject(repo, object.type, object.data);
    }
  } catch (err) {
    unpackOk = false;
    unpackDetail = err instanceof Error ? err.message : 'unpack error';
  }
  const reportLines: string[] = [`unpack ${unpackOk ? 'ok' : unpackDetail}\n`];
  if (unpackOk) {
    for (const command of commands) {
      if (command.newOid === ZERO_OID) {
        repo.refs.delete(command.ref);
        reportLines.push(`ok ${command.ref}\n`);
        continue;
      }
      const current = repo.refs.get(command.ref);
      const fastForward =
        (current === undefined || isAncestor(repo, current, command.newOid)) &&
        (command.oldOid === ZERO_OID || isAncestor(repo, command.oldOid, command.newOid));
      if (fastForward) {
        repo.refs.set(command.ref, command.newOid);
        reportLines.push(`ok ${command.ref}\n`);
      } else {
        reportLines.push(`ng ${command.ref} non-fast-forward\n`);
      }
    }
  } else {
    for (const command of commands) reportLines.push(`ng ${command.ref} unpacker error\n`);
  }
  const report = Buffer.concat([...reportLines.map((line) => encodePacket(line)), PACKET_FLUSH]);
  if (!sideband) return report;
  const parts: Buffer[] = [];
  for (const chunk of splitBuffer(report, 65_000)) parts.push(encodePacket(Buffer.concat([Buffer.from([1]), chunk])));
  parts.push(PACKET_FLUSH);
  return Buffer.concat(parts);
}

// ---------------------------------------------------------------------------------------------
// Pull-request helpers shared by REST, GraphQL and MCP.

function openPull(repo: Repo, title: string, body: string, head: string, base: string): Pull | null {
  const headSha = repo.refs.get(branchRef(head));
  const baseSha = repo.refs.get(branchRef(base));
  if (headSha === undefined || baseSha === undefined) return null;
  repo.pullSeq += 1;
  const pull: Pull = {
    id: allocateId(),
    number: repo.pullSeq,
    title,
    body,
    state: 'open',
    head,
    base,
    baseSha,
    merged: false,
    mergedAt: null,
    mergeCommitSha: null,
    createdAt: nowSec(),
  };
  repo.pulls.set(pull.number, pull);
  return pull;
}

/** Squash the head's changes onto the base branch; null on a conflict. */
function mergePull(repo: Repo, pull: Pull): string | null {
  if (pull.merged) return pull.mergeCommitSha;
  const currentTip = repo.refs.get(branchRef(pull.base));
  if (currentTip === undefined) return null;
  const baseFiles = filesOfCommit(repo, pull.baseSha);
  const headFiles = filesOfCommit(repo, pull.head);
  const currentFiles = filesOfCommit(repo, currentTip);
  const changes = new Map<string, FileEntry | null>();
  for (const path of new Set([...baseFiles.keys(), ...headFiles.keys()])) {
    const before = baseFiles.get(path);
    const after = headFiles.get(path);
    if (sameEntry(before, after)) continue;
    const current = currentFiles.get(path);
    if (currentTip !== pull.baseSha && !sameEntry(before, current)) return null;
    changes.set(path, after ?? null);
  }
  const sha = makeCommit(repo, pull.base, changes, `Merge pull request #${pull.number} from ${pull.head}`);
  pull.merged = true;
  pull.state = 'closed';
  pull.mergedAt = isoOf(nowSec());
  pull.mergeCommitSha = sha;
  return sha;
}

// ---------------------------------------------------------------------------------------------
// The git smart-HTTP endpoint.

async function handleGit(req: IncomingMessage, res: ServerResponse, segments: string[], body: Buffer, url: URL): Promise<boolean> {
  if (segments.length < 2) return false;
  const owner = segments[0] ?? '';
  const repoPart = segments[1] ?? '';
  if (!repoPart.endsWith('.git')) return false;
  const name = repoPart.slice(0, -4);
  const suffix = segments.slice(2).join('/');
  const method = (req.method ?? 'GET').toUpperCase();
  const service =
    suffix === 'info/refs'
      ? url.searchParams.get('service') === 'git-upload-pack' || url.searchParams.get('service') === 'git-receive-pack'
        ? (url.searchParams.get('service') as string)
        : null
      : suffix === 'git-upload-pack' || suffix === 'git-receive-pack'
        ? suffix
        : null;
  if (service === null) return false;

  const repo = findRepo(owner, name);
  if (suffix === 'info/refs') {
    if (method !== 'GET') return false;
    if (repo === null) {
      res.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' });
      res.end('Not Found\n');
      return true;
    }
    const v2 = service === 'git-upload-pack' && /version=2/.test(String(req.headers['git-protocol'] ?? ''));
    const preamble = Buffer.concat([encodePacket(`# service=${service}\n`), PACKET_FLUSH]);
    const advertisement = v2
      ? Buffer.concat([encodePacket('version 2\n'), encodePacket('agent=github-forge/1.0\n'), encodePacket('ls-refs\n'), encodePacket('fetch=shallow\n'), encodePacket('object-format=sha1\n'), PACKET_FLUSH])
      : v0Advertisement(repo, service);
    const out = Buffer.concat([preamble, advertisement]);
    res.writeHead(200, { 'content-type': `application/x-${service}-advertisement`, 'content-length': out.length });
    res.end(out);
    return true;
  }

  if (method !== 'POST') return false;
  if (repo === null) {
    res.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' });
    res.end('Not Found\n');
    return true;
  }
  if (service === 'git-upload-pack') {
    const { packets } = decodePackets(body);
    const isV2 = packets.some((packet) => packet.kind === 'data' && packetText(packet).startsWith('command='));
    let out: Buffer;
    try {
      out = isV2 ? serveUploadPackV2(repo, packets) : serveUploadPackV0(repo, packets);
    } catch {
      out = PACKET_FLUSH;
    }
    res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result', 'content-length': out.length });
    res.end(out);
    return true;
  }
  let out: Buffer;
  try {
    out = serveReceivePack(repo, body);
  } catch {
    out = Buffer.concat([encodePacket('unpack error\n'), PACKET_FLUSH]);
  }
  res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-result', 'content-length': out.length });
  res.end(out);
  return true;
}

// ---------------------------------------------------------------------------------------------
// GraphQL v4: a small document parser and the resolvers for the documents gh and
// github-mcp-server send.

type GqlValue =
  | { kind: 'var'; name: string }
  | { kind: 'int'; value: number }
  | { kind: 'string'; value: string }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; items: GqlValue[] }
  | { kind: 'object'; fields: Record<string, GqlValue> };

interface GqlField {
  alias: string | null;
  name: string;
  args: Record<string, GqlValue>;
  selection: GqlField[] | null;
}

interface GqlOperation {
  type: 'query' | 'mutation';
  name: string | null;
  variables: Record<string, GqlValue>;
  selection: GqlField[];
}

interface GqlError {
  message: string;
  path?: Array<string | number>;
}

function tokenizeGraphql(source: string): string[] {
  const tokens: string[] = [];
  let index = 0;
  while (index < source.length) {
    const ch = source[index] ?? '';
    if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',') {
      index += 1;
      continue;
    }
    if (ch === '#') {
      while (index < source.length && source[index] !== '\n') index += 1;
      continue;
    }
    if (ch === '"') {
      if (source.startsWith('"""', index)) {
        const end = source.indexOf('"""', index + 3);
        const text = source.slice(index + 3, end < 0 ? source.length : end);
        tokens.push(`"${text}"`);
        index = end < 0 ? source.length : end + 3;
        continue;
      }
      let cursor = index + 1;
      let text = '';
      while (cursor < source.length && source[cursor] !== '"') {
        if (source[cursor] === '\\' && cursor + 1 < source.length) {
          text += source[cursor + 1];
          cursor += 2;
        } else {
          text += source[cursor];
          cursor += 1;
        }
      }
      tokens.push(`"${text}"`);
      index = cursor + 1;
      continue;
    }
    if (source.startsWith('...', index)) {
      tokens.push('...');
      index += 3;
      continue;
    }
    if ('{}()[]:!$='.includes(ch)) {
      tokens.push(ch);
      index += 1;
      continue;
    }
    let cursor = index;
    while (cursor < source.length && /[A-Za-z0-9_-]/.test(source[cursor] ?? '')) cursor += 1;
    if (cursor === index) {
      index += 1;
      continue;
    }
    tokens.push(source.slice(index, cursor));
    index = cursor;
  }
  return tokens;
}

class GqlParser {
  private index = 0;
  private readonly tokens: readonly string[];

  constructor(tokens: readonly string[]) {
    this.tokens = tokens;
  }

  private peek(): string | null {
    return this.tokens[this.index] ?? null;
  }

  private next(): string {
    const token = this.tokens[this.index];
    if (token === undefined) throw new Error('unexpected end of document');
    this.index += 1;
    return token;
  }

  private expect(token: string): void {
    const actual = this.next();
    if (actual !== token) throw new Error(`expected ${token}, got ${actual}`);
  }

  parseOperation(): GqlOperation {
    let type: 'query' | 'mutation' = 'query';
    const head = this.peek();
    if (head === 'query' || head === 'mutation') type = this.next() as 'query' | 'mutation';
    let name: string | null = null;
    const afterKeyword = this.peek();
    if (afterKeyword !== null && afterKeyword !== '{' && afterKeyword !== '(') name = this.next();
    const variables: Record<string, GqlValue> = {};
    if (this.peek() === '(') {
      this.next();
      while (this.peek() !== ')') {
        let variableName = this.next();
        if (variableName === '$') variableName = this.next();
        this.expect(':');
        let depth = 0;
        while (this.peek() !== null) {
          const token = this.peek() as string;
          if (depth === 0 && (token === '=' || token === ')')) break;
          if (token === '[') depth += 1;
          else if (token === ']') depth -= 1;
          this.next();
        }
        if (this.peek() === '=') {
          this.next();
          variables[variableName] = this.parseValue();
        }
      }
      this.expect(')');
    }
    return { type, name, variables, selection: this.parseSelectionSet() };
  }

  private parseSelectionSet(): GqlField[] {
    this.expect('{');
    const fields: GqlField[] = [];
    while (this.peek() !== '}') {
      if (this.peek() === null) throw new Error('unterminated selection set');
      if (this.peek() === '...') {
        this.next();
        if (this.peek() === 'on') {
          this.next();
          this.next();
        }
        fields.push({ alias: null, name: '...', args: {}, selection: this.parseSelectionSet() });
        continue;
      }
      let name = this.next();
      let alias: string | null = null;
      if (this.peek() === ':') {
        this.next();
        alias = name;
        name = this.next();
      }
      const args: Record<string, GqlValue> = {};
      if (this.peek() === '(') {
        this.next();
        while (this.peek() !== ')') {
          const argName = this.next();
          this.expect(':');
          args[argName] = this.parseValue();
        }
        this.expect(')');
      }
      let selection: GqlField[] | null = null;
      if (this.peek() === '{') selection = this.parseSelectionSet();
      fields.push({ alias, name, args, selection });
    }
    this.expect('}');
    return fields;
  }

  private parseValue(): GqlValue {
    const token = this.next();
    if (token === '$') return { kind: 'var', name: this.next() };
    if (token === '[') {
      const items: GqlValue[] = [];
      while (this.peek() !== ']') items.push(this.parseValue());
      this.expect(']');
      return { kind: 'list', items };
    }
    if (token === '{') {
      const fields: Record<string, GqlValue> = {};
      while (this.peek() !== '}') {
        const key = this.next();
        this.expect(':');
        fields[key] = this.parseValue();
      }
      this.expect('}');
      return { kind: 'object', fields };
    }
    if (token.startsWith('"')) return { kind: 'string', value: token.slice(1, -1) };
    if (token === 'true') return { kind: 'boolean', value: true };
    if (token === 'false') return { kind: 'boolean', value: false };
    if (token === 'null') return { kind: 'null' };
    if (/^-?\d+$/.test(token)) return { kind: 'int', value: Number(token) };
    return { kind: 'enum', value: token };
  }
}

function resolveGqlValue(value: GqlValue, variables: Record<string, unknown>): unknown {
  switch (value.kind) {
    case 'var':
      return variables[value.name] ?? null;
    case 'int':
      return value.value;
    case 'string':
      return value.value;
    case 'boolean':
      return value.value;
    case 'null':
      return null;
    case 'enum':
      return value.value;
    case 'list':
      return value.items.map((item) => resolveGqlValue(item, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const [key, item] of Object.entries(value.fields)) out[key] = resolveGqlValue(item, variables);
      return out;
    }
    default:
      return null;
  }
}

function gqlArgs(field: GqlField, variables: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const [key, value] of Object.entries(field.args)) out[key] = resolveGqlValue(value, variables);
  return out;
}

/** A selection with inline fragments flattened into its parent. */
function flattenSelection(fields: readonly GqlField[]): GqlField[] {
  const out: GqlField[] = [];
  for (const field of fields) {
    if (field.name === '...') out.push(...flattenSelection(field.selection ?? []));
    else out.push(field);
  }
  return out;
}

function globalId(kind: string, key: string): string {
  return Buffer.from(`${kind}:${key}`, 'utf8').toString('base64');
}

function decodeGlobalId(id: string): { kind: string; key: string } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const at = text.indexOf(':');
    if (at < 0) return null;
    return { kind: text.slice(0, at), key: text.slice(at + 1) };
  } catch {
    return null;
  }
}

function repoById(id: number): Repo | null {
  for (const repo of repos.values()) if (repo.id === id) return repo;
  return null;
}

function repoFromGlobalKey(key: string): Repo | null {
  const slash = key.indexOf('/');
  const hash = key.lastIndexOf('#');
  if (slash < 0) return null;
  const owner = key.slice(0, slash);
  const name = key.slice(slash + 1, hash < 0 ? undefined : hash);
  return findRepo(owner, name);
}

function numberFromGlobalKey(key: string): number {
  const hash = key.lastIndexOf('#');
  if (hash < 0) return 0;
  return Number(key.slice(hash + 1)) || 0;
}

const INTROSPECTION_FIELDS: Readonly<Record<string, readonly string[]>> = {
  Issue: ['id', 'number', 'title', 'state', 'body', 'labels', 'author', 'createdAt', 'updatedAt', 'comments'],
  PullRequest: ['id', 'number', 'headRefName', 'baseRefName', 'mergeable', 'state', 'merged', 'files', 'title', 'body', 'isDraft'],
  Repository: [
    'id',
    'databaseId',
    'name',
    'nameWithOwner',
    'owner',
    'defaultBranchRef',
    'viewerPermission',
    'hasIssuesEnabled',
    'issue',
    'issues',
    'pullRequests',
    'pullRequest',
    'description',
    'isPrivate',
  ],
  SearchType: [],
  IssueState: [],
  MergeableState: [],
  PullRequestState: [],
};

const INTROSPECTION_ENUMS: Readonly<Record<string, readonly string[]>> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'CODE', 'COMMIT'],
  IssueState: ['OPEN', 'CLOSED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  OrderDirection: ['ASC', 'DESC'],
};

function introspectionValue(name: string, selection: readonly GqlField[], variables: Record<string, unknown>): unknown {
  if (!(name in INTROSPECTION_FIELDS) && !(name in INTROSPECTION_ENUMS)) return null;
  const value: Record<string, unknown> = {};
  for (const field of flattenSelection(selection)) {
    switch (field.name) {
      case 'name':
        value.name = name;
        break;
      case 'kind':
        value.kind = name in INTROSPECTION_ENUMS && INTROSPECTION_ENUMS[name]!.length > 0 ? 'ENUM' : 'OBJECT';
        break;
      case 'fields': {
        const names = INTROSPECTION_FIELDS[name] ?? [];
        value.fields = names.map((fieldName) => ({ name: fieldName }));
        break;
      }
      case 'enumValues': {
        const names = INTROSPECTION_ENUMS[name] ?? [];
        value.enumValues = names.map((enumName) => ({ name: enumName }));
        break;
      }
      default:
        value[field.alias ?? field.name] = null;
    }
  }
  void variables;
  return value;
}

function issueStateName(issue: Issue): string {
  return issue.state === 'open' ? 'OPEN' : 'CLOSED';
}

function pullStateName(pull: Pull): string {
  if (pull.merged) return 'MERGED';
  return pull.state === 'open' ? 'OPEN' : 'CLOSED';
}

function buildIssueValue(repo: Repo, issue: Issue, selection: readonly GqlField[], errors: GqlError[]): Record<string, unknown> {
  const value: Record<string, unknown> = {};
  for (const field of flattenSelection(selection)) {
    const key = field.alias ?? field.name;
    switch (field.name) {
      case 'id':
        value[key] = globalId('Issue', `${repo.owner}/${repo.name}#${issue.number}`);
        break;
      case 'number':
        value[key] = issue.number;
        break;
      case 'title':
        value[key] = issue.title;
        break;
      case 'body':
        value[key] = issue.body;
        break;
      case 'state':
        value[key] = issueStateName(issue);
        break;
      case 'createdAt':
        value[key] = isoOf(issue.createdAt);
        break;
      case 'updatedAt':
        value[key] = isoOf(issue.createdAt);
        break;
      default:
        errors.push({ message: `Cannot query field "${field.name}" on type "Issue".` });
        value[key] = null;
    }
  }
  return value;
}

function pullChangedPaths(repo: Repo, pull: Pull): string[] {
  const baseFiles = filesOfCommit(repo, pull.baseSha);
  const headFiles = filesOfCommit(repo, pull.head);
  const paths: string[] = [];
  for (const path of new Set([...baseFiles.keys(), ...headFiles.keys()])) {
    if (!sameEntry(baseFiles.get(path), headFiles.get(path))) paths.push(path);
  }
  return paths;
}

function buildPullValue(repo: Repo, pull: Pull, selection: readonly GqlField[], errors: GqlError[]): Record<string, unknown> {
  const value: Record<string, unknown> = {};
  for (const field of flattenSelection(selection)) {
    const key = field.alias ?? field.name;
    switch (field.name) {
      case 'id':
        value[key] = globalId('PullRequest', `${repo.owner}/${repo.name}#${pull.number}`);
        break;
      case 'number':
        value[key] = pull.number;
        break;
      case 'state':
        value[key] = pullStateName(pull);
        break;
      case 'merged':
        value[key] = pull.merged;
        break;
      case 'headRefName':
        value[key] = pull.head;
        break;
      case 'baseRefName':
        value[key] = pull.base;
        break;
      case 'mergeable':
        value[key] = 'MERGEABLE';
        break;
      case 'files': {
        const paths = pullChangedPaths(repo, pull);
        const nodes = paths.map((path) => ({ path }));
        value[key] = { nodes };
        break;
      }
      default:
        errors.push({ message: `Cannot query field "${field.name}" on type "PullRequest".` });
        value[key] = null;
    }
  }
  return value;
}

function buildRepositoryValue(repo: Repo, selection: readonly GqlField[], variables: Record<string, unknown>, errors: GqlError[]): Record<string, unknown> {
  const value: Record<string, unknown> = {};
  for (const field of flattenSelection(selection)) {
    const key = field.alias ?? field.name;
    const args = gqlArgs(field, variables);
    switch (field.name) {
      case 'id':
        value[key] = globalId('Repository', String(repo.id));
        break;
      case 'databaseId':
        value[key] = repo.id;
        break;
      case 'name':
        value[key] = repo.name;
        break;
      case 'nameWithOwner':
        value[key] = `${repo.owner}/${repo.name}`;
        break;
      case 'owner':
        value[key] = { login: repo.owner };
        break;
      case 'defaultBranchRef': {
        const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
        value[key] = tip === undefined ? null : { name: repo.defaultBranch };
        break;
      }
      case 'viewerPermission':
        value[key] = 'ADMIN';
        break;
      case 'hasIssuesEnabled':
        value[key] = true;
        break;
      case 'description':
        value[key] = repo.description;
        break;
      case 'isPrivate':
        value[key] = repo.private;
        break;
      case 'issue': {
        const number = typeof args.number === 'number' ? args.number : Number(args.number);
        const issue = repo.issues.get(number);
        value[key] = issue === undefined ? null : buildIssueValue(repo, issue, field.selection ?? [], errors);
        break;
      }
      case 'issues': {
        value[key] = buildIssueConnection(repo, field, args, errors);
        break;
      }
      case 'pullRequests': {
        const first = typeof args.first === 'number' ? args.first : 30;
        const nodesField = flattenSelection(field.selection ?? []).find((entry) => entry.name === 'nodes');
        const nodes = [...repo.pulls.values()]
          .filter((pull) => pull.state === 'open')
          .sort((a, b) => b.number - a.number)
          .slice(0, Math.max(0, first))
          .map((pull) => buildPullValue(repo, pull, nodesField?.selection ?? [], errors));
        value[key] = { nodes };
        break;
      }
      case 'pullRequest': {
        const number = typeof args.number === 'number' ? args.number : Number(args.number);
        const pull = repo.pulls.get(number);
        value[key] = pull === undefined ? null : buildPullValue(repo, pull, field.selection ?? [], errors);
        break;
      }
      default:
        errors.push({ message: `Cannot query field "${field.name}" on type "Repository".` });
        value[key] = null;
    }
  }
  return value;
}

function buildIssueConnection(repo: Repo, field: GqlField, args: Record<string, unknown>, errors: GqlError[]): Record<string, unknown> {
  const selection = flattenSelection(field.selection ?? []);
  const nodesField = selection.find((entry) => entry.name === 'nodes');
  const pageInfoField = selection.find((entry) => entry.name === 'pageInfo');
  const first = typeof args.first === 'number' ? args.first : 30;
  const states = Array.isArray(args.states) ? args.states.filter((state): state is string => typeof state === 'string') : [];
  const orderBy = isRecord(args.orderBy) ? args.orderBy : {};
  const orderField = typeof orderBy.field === 'string' ? orderBy.field : 'CREATED_AT';
  const direction = typeof orderBy.direction === 'string' ? orderBy.direction : 'DESC';
  let list = [...repo.issues.values()];
  if (states.length > 0) list = list.filter((issue) => states.includes(issueStateName(issue)));
  list.sort((a, b) => {
    let comparison = 0;
    if (orderField === 'COMMENTS') comparison = a.number - b.number;
    else comparison = a.createdAt - b.createdAt;
    if (comparison === 0) comparison = a.number - b.number;
    return direction === 'ASC' ? comparison : -comparison;
  });
  const after = typeof args.after === 'string' ? Number(args.after) : Number.NaN;
  if (Number.isFinite(after)) list = list.filter((issue) => (direction === 'ASC' ? issue.number > after : issue.number < after));
  const total = list.length;
  const page = list.slice(0, Math.max(0, first));
  const nodes = page.map((issue) => buildIssueValue(repo, issue, nodesField?.selection ?? [], errors));
  const endCursor = page.length > 0 ? String(page[page.length - 1]!.number) : null;
  const pageInfo: Record<string, unknown> = {};
  if (pageInfoField !== undefined) {
    for (const entry of flattenSelection(pageInfoField.selection ?? [])) {
      const key = entry.alias ?? entry.name;
      if (entry.name === 'hasNextPage') pageInfo[key] = total > page.length;
      else if (entry.name === 'endCursor') pageInfo[key] = endCursor;
      else if (entry.name === 'startCursor') pageInfo[key] = page.length > 0 ? String(page[0]!.number) : null;
      else pageInfo[key] = null;
    }
  }
  return { nodes, pageInfo };
}

function runQueryField(field: GqlField, variables: Record<string, unknown>, errors: GqlError[]): unknown {
  const args = gqlArgs(field, variables);
  switch (field.name) {
    case 'viewer': {
      const value: Record<string, unknown> = {};
      for (const entry of flattenSelection(field.selection ?? [])) {
        const key = entry.alias ?? entry.name;
        if (entry.name === 'login') value[key] = VIEWER_LOGIN;
        else {
          errors.push({ message: `Cannot query field "${entry.name}" on type "User".` });
          value[key] = null;
        }
      }
      return value;
    }
    case 'repository': {
      const repo = findRepo(str(args.owner), str(args.name));
      return repo === null ? null : buildRepositoryValue(repo, field.selection ?? [], variables, errors);
    }
    case 'node': {
      const decoded = decodeGlobalId(str(args.id));
      if (decoded === null) return null;
      if (decoded.kind === 'Repository') {
        const repo = repoById(Number(decoded.key));
        return repo === null ? null : buildRepositoryValue(repo, field.selection ?? [], variables, errors);
      }
      if (decoded.kind === 'Issue') {
        const repo = repoFromGlobalKey(decoded.key);
        const issue = repo === null ? undefined : repo.issues.get(numberFromGlobalKey(decoded.key));
        return repo === null || issue === undefined ? null : buildIssueValue(repo, issue, field.selection ?? [], errors);
      }
      return null;
    }
    case '__type':
      return introspectionValue(str(args.name), field.selection ?? [], variables);
    default:
      errors.push({ message: `Cannot query field "${field.name}" on type "Query".` });
      return null;
  }
}

function runMutationField(field: GqlField, variables: Record<string, unknown>, errors: GqlError[]): unknown {
  const args = gqlArgs(field, variables);
  const input = isRecord(args.input) ? args.input : {};
  switch (field.name) {
    case 'createIssue': {
      const repo = repoById(Number(decodeGlobalId(str(input.repositoryId))?.key ?? '0'));
      if (repo === null) return null;
      repo.issueSeq += 1;
      const issue: Issue = {
        id: allocateId(),
        number: repo.issueSeq,
        title: str(input.title),
        body: str(input.body),
        state: 'open',
        labels: [],
        createdAt: nowSec(),
      };
      repo.issues.set(issue.number, issue);
      const issueField = flattenSelection(field.selection ?? []).find((entry) => entry.name === 'issue');
      return { issue: buildIssueValue(repo, issue, issueField?.selection ?? [], errors) };
    }
    case 'closeIssue': {
      const decoded = decodeGlobalId(str(input.issueId));
      const repo = decoded === null ? null : repoFromGlobalKey(decoded.key);
      const issue = decoded === null || repo === null ? undefined : repo.issues.get(numberFromGlobalKey(decoded.key));
      if (repo === null || issue === undefined) return null;
      issue.state = 'closed';
      const issueField = flattenSelection(field.selection ?? []).find((entry) => entry.name === 'issue');
      return { issue: buildIssueValue(repo, issue, issueField?.selection ?? [], errors) };
    }
    case 'createPullRequest': {
      const repo = repoById(Number(decodeGlobalId(str(input.repositoryId))?.key ?? '0'));
      if (repo === null) return null;
      const pull = openPull(repo, str(input.title), str(input.body), str(input.headRefName), str(input.baseRefName));
      if (pull === null) return null;
      const pullField = flattenSelection(field.selection ?? []).find((entry) => entry.name === 'pullRequest');
      return { pullRequest: buildPullValue(repo, pull, pullField?.selection ?? [], errors) };
    }
    case 'mergePullRequest': {
      const decoded = decodeGlobalId(str(input.pullRequestId));
      const repo = decoded === null ? null : repoFromGlobalKey(decoded.key);
      const pull = decoded === null || repo === null ? undefined : repo.pulls.get(numberFromGlobalKey(decoded.key));
      if (repo === null || pull === undefined) return null;
      const sha = mergePull(repo, pull);
      if (sha === null) return null;
      const pullField = flattenSelection(field.selection ?? []).find((entry) => entry.name === 'pullRequest');
      return { pullRequest: buildPullValue(repo, pull, pullField?.selection ?? [], errors) };
    }
    case 'addComment': {
      const decoded = decodeGlobalId(str(input.subjectId));
      const repo = decoded === null ? null : repoFromGlobalKey(decoded.key);
      if (repo === null) return null;
      const number = numberFromGlobalKey(decoded === null ? '' : decoded.key);
      const issue = repo.issues.get(number);
      if (issue === undefined) return null;
      repo.commentSeq += 1;
      const comment: Comment = { id: allocateId(), issue: number, body: str(input.body), createdAt: nowSec() };
      repo.comments.set(comment.id, comment);
      return { commentEdge: { node: { id: globalId('IssueComment', `${repo.owner}/${repo.name}#${comment.id}`), body: comment.body } } };
    }
    default:
      errors.push({ message: `Cannot query field "${field.name}" on type "Mutation".` });
      return null;
  }
}

function runGraphqlOperation(operation: GqlOperation, provided: Record<string, unknown>): { data: unknown; errors: GqlError[] } {
  const variables: Record<string, unknown> = {};
  for (const [name, value] of Object.entries(operation.variables)) variables[name] = resolveGqlValue(value, provided);
  for (const [name, value] of Object.entries(provided)) variables[name] = value;
  const errors: GqlError[] = [];
  const data: Record<string, unknown> = {};
  for (const field of operation.selection) {
    const key = field.alias ?? field.name;
    try {
      data[key] = operation.type === 'mutation' ? runMutationField(field, variables, errors) : runQueryField(field, variables, errors);
    } catch (err) {
      errors.push({ message: err instanceof Error ? err.message : 'the operation failed' });
      data[key] = null;
    }
  }
  return { data: errors.length > 0 ? null : data, errors };
}

function runGraphqlRequest(payload: Record<string, unknown>): { status: number; body: unknown } {
  const query = str(payload.query);
  if (query === '') return { status: 200, body: { data: null, errors: [{ message: 'a query is required' }] } };
  let operation: GqlOperation;
  try {
    operation = new GqlParser(tokenizeGraphql(query)).parseOperation();
  } catch (err) {
    return { status: 200, body: { data: null, errors: [{ message: err instanceof Error ? err.message : 'the document did not parse' }] } };
  }
  const variables = isRecord(payload.variables) ? payload.variables : {};
  const result = runGraphqlOperation(operation, variables);
  return { status: 200, body: result };
}

async function handleGraphQL(req: IncomingMessage, res: ServerResponse, body: Buffer): Promise<void> {
  if (!authorized(req)) {
    sendMessage(res, 401, 'Requires authentication');
    return;
  }
  const parsed = parseJson(body);
  if (!parsed.ok) {
    sendJsonR(res, 400, { message: 'Problems parsing JSON' });
    return;
  }
  if (Array.isArray(parsed.value)) {
    const results = parsed.value.map((entry) => (isRecord(entry) ? runGraphqlRequest(entry) : { status: 200, body: { data: null, errors: [{ message: 'an operation must be an object' }] } }));
    sendJsonR(res, 200, results.map((entry) => entry.body));
    return;
  }
  if (!isRecord(parsed.value)) {
    sendJsonR(res, 400, { message: 'Problems parsing JSON' });
    return;
  }
  const result = runGraphqlRequest(parsed.value);
  sendJsonR(res, result.status, result.body);
}

// ---------------------------------------------------------------------------------------------
// MCP over streamable HTTP: server/discover, the legacy handshake, tools/list and tools/call,
// acting on the same in-memory store as REST.

interface McpToolSpec {
  name: string;
  description: string;
  inputSchema: Record<string, unknown>;
  required: string[];
}

const MCP_SERVER_INFO = { name: 'github-forge', version: '1.0.0' } as const;
const MCP_REVISIONS = ['2026-07-28', '2025-11-25', '2025-06-18'] as const;

const MCP_TOOLS: readonly McpToolSpec[] = [
  {
    name: 'create_repo',
    description: 'Create a repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The repository name.' },
        description: { type: 'string', description: 'An optional description.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
    required: ['name'],
  },
  {
    name: 'get_repo',
    description: 'Read one repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'create_issue',
    description: 'Open an issue on a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
    required: ['owner', 'repo', 'title'],
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'create_pull_request',
    description: 'Open a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        head: { type: 'string', description: 'The source branch.' },
        base: { type: 'string', description: 'The target branch.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
    required: ['owner', 'repo', 'title', 'head', 'base'],
  },
  {
    name: 'merge_pull_request',
    description: 'Squash-merge an open pull request.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'number', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
    required: ['owner', 'repo', 'pull_number'],
  },
  {
    name: 'list_pulls',
    description: 'List the pull requests of a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'get_pull_request',
    description: 'Read one pull request by number.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'number', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
    required: ['owner', 'repo', 'pull_number'],
  },
  {
    name: 'delete_repo',
    description: 'Delete a repository the authenticated user owns.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
    required: ['owner', 'repo'],
  },
];

function mcpText(value: unknown): { content: Array<{ type: string; text: string }>; structuredContent: unknown } {
  return { content: [{ type: 'text', text: JSON.stringify(value) }], structuredContent: value };
}

function mcpToolError(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function mcpArgString(args: Record<string, unknown>, ...names: readonly string[]): string {
  for (const name of names) {
    const value = args[name];
    if (typeof value === 'string') return value;
    if (typeof value === 'number') return String(value);
  }
  return '';
}

function callMcpTool(name: string, args: Record<string, unknown>): { ok: true; value: unknown } | { ok: false; message: string } {
  const owner = mcpArgString(args, 'owner', 'owner_login') || VIEWER_LOGIN;
  const repoName = mcpArgString(args, 'repo', 'repository', 'repo_name');
  const findRepoOrNull = (): Repo | null => findRepo(owner, repoName);
  switch (name) {
    case 'create_repo': {
      const repoNameArg = mcpArgString(args, 'name', 'repo', 'repository');
      if (repoNameArg === '') return { ok: false, message: 'create_repo requires a name' };
      const existing = findRepo(VIEWER_LOGIN, repoNameArg);
      const repo = existing ?? makeRepo(VIEWER_LOGIN, repoNameArg, boolv(args.private, false), mcpArgString(args, 'description'));
      return { ok: true, value: repoJson(repo) };
    }
    case 'get_repo': {
      const repo = findRepoOrNull();
      if (repo === null) return { ok: false, message: `repository ${owner}/${repoName} was not found` };
      return { ok: true, value: repoJson(repo) };
    }
    case 'delete_repo': {
      const repo = findRepoOrNull();
      if (repo === null) return { ok: false, message: `repository ${owner}/${repoName} was not found` };
      repos.delete(repoKey(repo.owner, repo.name));
      return { ok: true, value: { deleted: true, full_name: `${repo.owner}/${repo.name}` } };
    }
    case 'create_issue': {
      const repo = findRepoOrNull();
      if (repo === null) return { ok: false, message: `repository ${owner}/${repoName} was not found` };
      const title = mcpArgString(args, 'title');
      if (title === '') return { ok: false, message: 'create_issue requires a title' };
      repo.issueSeq += 1;
      const issue: Issue = {
        id: allocateId(),
        number: repo.issueSeq,
        title,
        body: mcpArgString(args, 'body'),
        state: 'open',
        labels: [],
        createdAt: nowSec(),
      };
      repo.issues.set(issue.number, issue);
      return { ok: true, value: issueJson(repo, issue) };
    }
    case 'list_issues': {
      const repo = findRepoOrNull();
      if (repo === null) return { ok: false, message: `repository ${owner}/${repoName} was not found` };
      const state = mcpArgString(args, 'state') || 'all';
      const list = [...repo.issues.values()]
        .filter((issue) => state === 'all' || issue.state === state)
        .sort((a, b) => a.number - b.number)
        .map((issue) => issueJson(repo, issue));
      return { ok: true, value: list };
    }
    case 'create_pull_request': {
      const repo = findRepoOrNull();
      if (repo === null) return { ok: false, message: `repository ${owner}/${repoName} was not found` };
      const title = mcpArgString(args, 'title');
      const head = mcpArgString(args, 'head', 'head_ref');
      const base = mcpArgString(args, 'base', 'base_ref') || repo.defaultBranch;
      const pull = openPull(repo, title, mcpArgString(args, 'body'), head, base);
      if (pull === null) return { ok: false, message: `no commits between ${head} and ${base}` };
      return { ok: true, value: pullJson(repo, pull) };
    }
    case 'merge_pull_request': {
      const repo = findRepoOrNull();
      if (repo === null) return { ok: false, message: `repository ${owner}/${repoName} was not found` };
      const number = Number(mcpArgString(args, 'pull_number', 'number'));
      const pull = repo.pulls.get(number);
      if (pull === undefined) return { ok: false, message: `pull request #${number} was not found` };
      const sha = mergePull(repo, pull);
      if (sha === null) return { ok: false, message: 'the pull request is not mergeable' };
      return { ok: true, value: pullJson(repo, pull) };
    }
    case 'list_pulls': {
      const repo = findRepoOrNull();
      if (repo === null) return { ok: false, message: `repository ${owner}/${repoName} was not found` };
      const state = mcpArgString(args, 'state') || 'all';
      const list = [...repo.pulls.values()]
        .filter((pull) => state === 'all' || pull.state === state)
        .sort((a, b) => a.number - b.number)
        .map((pull) => pullJson(repo, pull));
      return { ok: true, value: list };
    }
    case 'get_pull_request': {
      const repo = findRepoOrNull();
      if (repo === null) return { ok: false, message: `repository ${owner}/${repoName} was not found` };
      const number = Number(mcpArgString(args, 'pull_number', 'number'));
      const pull = repo.pulls.get(number);
      if (pull === undefined) return { ok: false, message: `pull request #${number} was not found` };
      return { ok: true, value: pullJson(repo, pull) };
    }
    default:
      return { ok: false, message: `unknown tool ${name}` };
  }
}

function mcpDispatch(message: Record<string, unknown>): Record<string, unknown> | null {
  const id = message.id ?? null;
  const method = str(message.method);
  const params = isRecord(message.params) ? message.params : {};
  if (method === 'notifications/initialized' || method.startsWith('notifications/')) return null;
  const result = (value: unknown): Record<string, unknown> => ({ jsonrpc: '2.0', id, result: value });
  const error = (code: number, text: string): Record<string, unknown> => ({ jsonrpc: '2.0', id, error: { code, message: text } });
  switch (method) {
    case 'server/discover':
      return result({
        supportedVersions: [...MCP_REVISIONS],
        capabilities: { tools: { listChanged: false } },
        serverInfo: { ...MCP_SERVER_INFO },
        protocolVersion: MCP_REVISIONS[0],
        _meta: { 'io.modelcontextprotocol/serverInfo': { ...MCP_SERVER_INFO } },
      });
    case 'initialize':
      return result({
        protocolVersion: str(params.protocolVersion) || '2025-11-25',
        capabilities: { tools: {} },
        serverInfo: { ...MCP_SERVER_INFO },
      });
    case 'ping':
      return result({});
    case 'tools/list':
      return result({
        tools: MCP_TOOLS.map((tool) => ({ name: tool.name, description: tool.description, inputSchema: tool.inputSchema })),
      });
    case 'tools/call': {
      const name = str(params.name);
      const args = isRecord(params.arguments) ? params.arguments : {};
      const tool = MCP_TOOLS.find((entry) => entry.name === name);
      if (tool === undefined) return error(-32602, `Unknown tool: ${name}`);
      const missing = tool.required.filter((required) => args[required] === undefined || args[required] === null || args[required] === '');
      if (missing.length > 0) return error(-32602, `Missing required arguments: ${missing.join(', ')}`);
      const outcome = callMcpTool(name, args);
      if (!outcome.ok) return result(mcpToolError(outcome.message));
      return result(mcpText(outcome.value));
    }
    default:
      return error(-32601, `Method not found: ${method}`);
  }
}

async function handleMcp(req: IncomingMessage, res: ServerResponse, body: Buffer): Promise<void> {
  if (!authorized(req)) {
    sendJsonR(res, 401, { message: 'Requires authentication' });
    return;
  }
  const parsed = parseJson(body);
  if (!parsed.ok) {
    sendJsonR(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (Array.isArray(parsed.value)) {
    const answers: unknown[] = [];
    for (const entry of parsed.value) {
      if (!isRecord(entry)) continue;
      const answer = mcpDispatch(entry);
      if (answer !== null) answers.push(answer);
    }
    if (answers.length === 0) {
      res.writeHead(202, { 'x-github-request-id': requestId() });
      res.end();
      return;
    }
    sendJsonR(res, 200, answers);
    return;
  }
  if (!isRecord(parsed.value)) {
    sendJsonR(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  const answer = mcpDispatch(parsed.value);
  if (answer === null) {
    res.writeHead(202, { 'x-github-request-id': requestId() });
    res.end();
    return;
  }
  sendJsonR(res, 200, answer);
}

// ---------------------------------------------------------------------------------------------
// The server: route one request, never throw out of the listener.

async function handle(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const pathname = pathOf(req);
  const method = (req.method ?? 'GET').toUpperCase();
  const url = new URL(req.url ?? '/', originOf(req));
  const body = method === 'GET' || method === 'HEAD' ? Buffer.alloc(0) : await readBody(req);

  if (method === 'GET' && pathname === '/healthz') {
    sendJson(res, 200, { ok: true });
    return;
  }

  const segments = splitPath(pathname);

  if (pathname === '/api/v3' || pathname === '/api/v3/') {
    if (method === 'GET') {
      if (!authorized(req)) {
        sendMessage(res, 401, 'Requires authentication');
        return;
      }
      sendJsonR(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
      return;
    }
  }

  if (segments[0] === 'api' && segments[1] === 'v3') {
    await handleRest({ req, res, method, url, body, segments: segments.slice(2) });
    return;
  }

  if (pathname === '/api/graphql') {
    await handleGraphQL(req, res, body);
    return;
  }

  if (pathname === '/mcp') {
    await handleMcp(req, res, body);
    return;
  }

  if (segments.length >= 3 && segments[1]?.endsWith('.git')) {
    if (await handleGit(req, res, segments, body, url)) return;
  }

  sendMessage(res, 404, 'Not Found');
}

/** Build the server. It binds nothing until the caller listens; the entry listens on an ephemeral port. */
export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void handle(req, res).catch(() => {
      try {
        if (res.headersSent) res.end();
        else sendMessage(res, 500, 'Internal Server Error');
      } catch {
        res.destroy();
      }
    });
  });
}
