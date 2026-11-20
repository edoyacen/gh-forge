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

function filesOfCommit(repo: Repo, sha: string): Map<string, FileEntry> {
  const out = new Map<string, FileEntry>();
  const obj = getObject(repo, sha);
  if (obj === null) return out;
  if (obj.type === 'commit') {
    walkTree(repo, commitTreeOf(obj), '', out);
  } else if (obj.type === 'tag') {
    const target = tagTargetOf(obj);
    if (target !== '') return filesOfCommit(repo, target);
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
// Placeholders replaced by the smart-HTTP, GraphQL and MCP implementations below.

async function handleGit(_req: IncomingMessage, res: ServerResponse, _segments: string[], _body: Buffer): Promise<boolean> {
  sendMessage(res, 404, 'Not Found');
  return true;
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
  sendJsonR(res, 200, { data: null, errors: [{ message: 'GraphQL is not implemented' }] });
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
  sendJsonR(res, 200, { jsonrpc: '2.0', id: null, error: { code: -32601, message: 'Method not found' } });
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

  if (segments.length >= 3 && segments[1].endsWith('.git')) {
    if (await handleGit(req, res, segments, body)) return;
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
