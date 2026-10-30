// Mobile Py IDE — frontend.
//
// Loads CodeMirror 6 from a CDN for a real editor, with a plain-textarea
// fallback if that fails. Runs code through the streaming API so that
// input() works live: the program prints a prompt, you type a line and press
// Enter, and it continues — just like a terminal.

// index.html loads us as main.js?v=<build>. Carry that same stamp to the files
// we import, or a cached copy of one of them could still be served after a
// deploy — which is exactly how a fix can look like it did not work.
const BUILD_QUERY = new URL(import.meta.url).search;
let dl;
try {
  dl = await import(`./download.js${BUILD_QUERY}`);
} catch {
  dl = await import('./download.js'); // unstamped fallback
}
const { downloadPython, pythonFilename, canShareFiles, sharePython, copyText } = dl;

const DEFAULT_CODE = `# Mobile Py IDE — a live console
name = input("What is your name? ")
print("Hello,", name, "!")

for i in range(1, 4):
    print(i, "squared is", i * i)
`;

const STORAGE_CODE = 'mobi-py-code';
const STORAGE_STDIN = 'mobi-py-stdin';

const $ = (sel) => document.querySelector(sel);
const editorMount = $('#editorMount');
const fallback = $('#editorFallback');
const output = $('#output');
const statusEl = $('#status');
const stdinEl = $('#stdin');
const runBtn = $('#runBtn');
const runLabel = $('#runLabel');
const runIcon = document.querySelector('.run-icon');
const clearBtn = $('#clearBtn');
const fileNameInput = $('#fileName');
const downloadBtn = $('#downloadBtn');
const saveMoreBtn = $('#saveMoreBtn');
const saveDialog = $('#saveDialog');
const saveDownload = $('#saveDownload');
const saveServer = $('#saveServer');
const saveShare = $('#saveShare');
const saveCopy = $('#saveCopy');
const saveOut = $('#saveOut');
const inputForm = $('#inputForm');
const inputLine = $('#inputLine');
const sendBtn = $('#sendBtn');
const posBtn = $('#posBtn');
const consolePanel = $('#console');
const prefillDetails = $('#prefillDetails');
const prefillCount = $('#prefillCount');
const prefillClear = $('#prefillClear');
const modebar = $('#modebar');
const editorPanel = $('#editor');
const codeTab = document.querySelector('.tab[data-tab="editor"]');
const inputRow = $('#inputForm');
const pkgBtn = $('#pkgBtn');
const pkgDialog = $('#pkgDialog');
const pkgInput = $('#pkgInput');
const pkgInstall = $('#pkgInstall');
const pkgOut = $('#pkgOut');
const pkgAllowed = $('#pkgAllowed');
const pkgInstalled = $('#pkgInstalled');
const filesBtn = $('#filesBtn');
const filesDialog = $('#filesDialog');
const fileInput = $('#fileInput');
const uploadBtn = $('#uploadBtn');
const fileList = $('#fileList');
const fileOut = $('#fileOut');

let cmView = null;
let usingCM = false;
// The editor commands (undo, redo, indent) — loaded with CodeMirror.
let cmCommands = null;
let fallbackHistory = [];
let fallbackHistoryIndex = -1;
let fallbackHistoryAt = 0;
let es = null;
let runId = null;
let outputEmpty = true;
let mode = 'script';
let receivedEvents = false;
let lastRunEventId = 0;
// What the current run wrote to stderr, so a traceback can be read back later.
let runStderr = '';
// True when the run is under a real pseudoterminal, which changes what comes
// back (raw bytes, not text) and whether we need to echo what you type.
let runIsPty = false;
// Silence is ambiguous: a program may be thinking, or it may be waiting for a
// connection that will never come. Say something rather than show nothing.
let lastOutputAt = Date.now();
let quietNoted = false;
setInterval(() => {
  if (!runId) { quietNoted = false; return; }
  if (Date.now() - lastOutputAt < 10000) return;
  if (quietNoted) return;
  quietNoted = true;
  // Worded as information, not as a fault: sitting at a prompt is a perfectly
  // healthy silence, and this should not read like an error.
  appendOutput('… waiting — the session is still open. ■ Stop ends it.\n', 'muted');
}, 2000);
let spaceTtlHours = 24;
let filesAtStart = null;

/* ----------------------------- editor -------------------------------- */
function loadStored(key, def) {
  try { return localStorage.getItem(key) ?? def; } catch { return def; }
}
function getCode() {
  return usingCM ? cmView.state.doc.toString() : fallback.value;
}
function setCode(v) {
  if (usingCM) cmView.dispatch({ changes: { from: 0, to: cmView.state.doc.length, insert: v } });
  else fallback.value = v;
}

let saveTimer;
function saveCode() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    try { localStorage.setItem(STORAGE_CODE, getCode()); } catch { /* quota */ }
  }, 400);
}

/* ------------------- showing Python's shape in the editor --------------- */
// Python has no braces: a block *is* its indentation, and on a phone that is
// hard to see. Two quiet things are drawn — a faint rule at each indent level,
// and that rule in the accent colour where it holds the block the cursor is
// sitting in. The block is deliberately *not* shaded: a tint over a group of
// lines reads as a text selection, and the vertical line says the same thing
// without the ambiguity.

const SCAN_LIMIT = 4000; // a cursor move must never walk a huge file

function indentOf(text) {
  return text.match(/^[ \t]*/)[0].replace(/\t/g, '    ').length;
}
function isBlockOpener(text) {
  return /:\s*(#.*)?$/.test(text.trimEnd());
}

// The innermost block the cursor sits in, or null. `base` is the indent of the
// line that opens it, in spaces.
function activeBlock(view) {
  const doc = view.state.doc;
  const here = doc.lineAt(view.state.selection.main.head);
  let startNo = here.number;
  let base = indentOf(here.text);

  // If the cursor is not on a line that opens a block, find the nearest line
  // above it that is indented less — that is the block it sits inside.
  if (!isBlockOpener(here.text)) {
    let seen = 0;
    for (let n = here.number - 1; n >= 1 && seen < SCAN_LIMIT; n--, seen++) {
      const t = doc.line(n).text;
      if (!t.trim()) continue;
      const ind = indentOf(t);
      if (ind < base) { startNo = n; base = ind; break; }
    }
  }
  if (!isBlockOpener(doc.line(startNo).text)) return null;

  let endNo = startNo;
  let seen = 0;
  for (let n = startNo + 1; n <= doc.lines && seen < SCAN_LIMIT; n++, seen++) {
    const t = doc.line(n).text;
    if (!t.trim()) { endNo = n; continue; }
    if (indentOf(t) <= base) break;
    endNo = n;
  }
  // A blank line before the next statement is not really part of the block, and
  // tinting it makes the block look one line longer than it is.
  while (endNo > startNo && !doc.line(endNo).text.trim()) endNo--;
  if (endNo <= startNo) return null;
  return { start: startNo, end: endNo, base };
}

function pythonStructure(viewMod, stateMod) {
  const { ViewPlugin, Decoration } = viewMod;
  const { RangeSetBuilder } = stateMod;

  function build(view) {
    const doc = view.state.doc;
    const depth = new Map();

    // Only calculate guide depths for lines CodeMirror may draw. Resolving
    // blank lines looks ahead once per visible range, bounded on huge files.
    for (const range of view.visibleRanges) {
      const first = doc.lineAt(range.from).number;
      const last = doc.lineAt(range.to).number;
      let nextDepth = 0;
      for (let n = last + 1, scanned = 0; n <= doc.lines && scanned < SCAN_LIMIT; n++, scanned++) {
        const text = doc.line(n).text;
        if (text.trim()) {
          nextDepth = Math.min(12, Math.floor(indentOf(text) / 4));
          break;
        }
      }
      for (let n = last; n >= first; n--) {
        const text = doc.line(n).text;
        if (text.trim()) nextDepth = Math.min(12, Math.floor(indentOf(text) / 4));
        depth.set(n, nextDepth);
      }
    }

    const block = activeBlock(view);
    const hlAt = block ? `${block.base}ch` : '-20px';

    const builder = new RangeSetBuilder();
    for (const { from, to } of view.visibleRanges) {
      let pos = from;
      while (pos <= to) {
        const line = doc.lineAt(pos);
        const n = line.number;
        const d = depth.get(n) ?? 0;
        const inBody = Boolean(block) && n > block.start && n <= block.end;
        // The wrap indent is the line's own indentation, so a long line that
        // wraps continues under the code rather than at column 0.
        const indent = line.text.trim() ? indentOf(line.text) : 0;
        builder.add(line.from, line.from, Decoration.line({
          class: 'cm-guide',
          attributes: {
            style: `--guide-depth:${d};--hl-pos:${inBody ? hlAt : '-20px'};--wrap-indent:${indent}ch`,
          },
        }));
        if (line.to >= doc.length) break;
        pos = line.to + 1;
      }
    }
    return builder.finish();
  }

  return ViewPlugin.fromClass(class {
    constructor(view) { this.decorations = build(view); }
    update(u) {
      if (u.docChanged || u.selectionSet || u.viewportChanged) this.decorations = build(u.view);
    }
  }, { decorations: (v) => v.decorations });
}

async function initEditor() {
  const initial = loadStored(STORAGE_CODE, DEFAULT_CODE);
  // Show the saved code straight away, in the plain editor. CodeMirror arrives
  // over the network, and until it does this textarea is what the reader sees —
  // an empty one for a few seconds, and anything typed into it was thrown away
  // the moment CodeMirror took over.
  fallback.value = initial;
  fallbackHistory = [{ value: initial, start: 0, end: 0 }];
  fallbackHistoryIndex = 0;
  fallback.addEventListener('input', () => { saveCode(); recordFallbackHistory(); });
  fallback.addEventListener('keydown', handleFallbackKeydown);
  try {
    const [cm, py, theme, commands, lang, cmView2, cmState] = await Promise.all([
      import('https://esm.sh/codemirror@6.0.1'),
      import('https://esm.sh/@codemirror/lang-python@6.1.6'),
      import('https://esm.sh/@codemirror/theme-one-dark@6.1.2'),
      // Again the specifier basicSetup itself uses: undo and redo act on the
      // history that instance owns, so a second copy would do nothing.
      import('https://esm.sh/@codemirror/commands@^6.0.0?target=es2022'),
      // The exact specifier @codemirror/lang-python itself imports — a different
      // one would be a second copy of the package, and its settings ignored.
      import('https://esm.sh/@codemirror/language@^6.8.0?target=es2022'),
      // The specifiers basicSetup itself pulls in, so these are the same copies
      // and their decorations belong to the same editor.
      import('https://esm.sh/@codemirror/view@^6.0.0?target=es2022'),
      import('https://esm.sh/@codemirror/state@^6.0.0?target=es2022'),
    ]);
    cmCommands = commands;
    // Whatever is in the plain editor now: the saved code, or the reader's own
    // typing if they got there before CodeMirror did.
    const seed = fallback.value;

    cmView = new cm.EditorView({
      doc: seed,
      extensions: [
        cm.basicSetup,
        py.python(),
        // Without this the editor indents new lines by two spaces while the Tab
        // button inserts four, and the file ends up with both.
        lang.indentUnit.of('    '),
        theme.oneDark,
        pythonStructure(cmView2, cmState),
        cm.EditorView.lineWrapping,
        cm.EditorView.theme({
          '&': { height: '100%', fontSize: '15px' },
          '.cm-scroller': { fontFamily: 'var(--mono)', lineHeight: '1.5' },
          '.cm-content': { paddingBottom: '30vh' },
          '&.cm-focused': { outline: 'none' },
        }),
        cm.EditorView.updateListener.of((u) => { if (u.docChanged) saveCode(); }),
      ],
      parent: editorMount,
    });

    usingCM = true;
    editorMount.style.display = 'block';
    fallback.style.display = 'none';
    editorMount.addEventListener('keydown', (e) => {
      if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') { e.preventDefault(); onRunClick(); }
    });
  } catch (err) {
    console.warn('CodeMirror unavailable, using plain editor:', err);
    usingCM = false;
    editorMount.style.display = 'none';
    fallback.style.display = 'block';
  }
}

/* ----------------------------- tabs ---------------------------------- */
function switchTab(name) {
  document.querySelectorAll('.tab').forEach((t) => t.classList.toggle('active', t.dataset.tab === name));
  document.querySelectorAll('.panel').forEach((p) => p.classList.toggle('active', p.id === name));
  if (name === 'editor' && usingCM) setTimeout(() => cmView.requestMeasure(), 0);
  if (name === 'console' && termFit && !termMount.hidden) {
    requestAnimationFrame(() => {
      try { termFit.fit(); } catch { /* ignore */ }
    });
  }
}
document.querySelectorAll('.tab').forEach((t) => t.addEventListener('click', () => switchTab(t.dataset.tab)));

/* ------------------------- symbol toolbar ----------------------------- */
// Where the toolbar types: the editor in Script mode, the console's input line
// in REPL and Terminal — where the editor is hidden, so typing at it would go
// nowhere visible.
function targetIsInput() { return mode !== 'script'; }

function insertAtCursor(el, text, back) {
  const start = el.selectionStart ?? el.value.length;
  const end = el.selectionEnd ?? start;
  el.value = el.value.slice(0, start) + text + el.value.slice(end);
  const pos = Math.max(0, start + text.length - back);
  el.selectionStart = el.selectionEnd = pos;
  el.focus();
  el.dispatchEvent(new Event('input', { bubbles: true }));
}

function insertText(text, back = 0) {
  if (targetIsInput()) { insertAtCursor(inputLine, text, back); return; }
  const closers = new Set([')', ']', '}', '"', "'"]);
  if (usingCM) {
    const range = cmView.state.selection.main;
    if (range.empty && closers.has(text) && cmView.state.doc.sliceString(range.head, range.head + 1) === text) {
      cmView.dispatch({ selection: { anchor: range.head + 1 } });
      cmView.focus();
      return;
    }
    cmView.dispatch(cmView.state.replaceSelection(text));
    if (back) {
      const pos = cmView.state.selection.main.head - back;
      cmView.dispatch({ selection: { anchor: pos } });
    }
    cmView.focus();
  } else {
    if (fallback.selectionStart === fallback.selectionEnd && closers.has(text)
        && fallback.value[fallback.selectionStart] === text) {
      fallback.setSelectionRange(fallback.selectionStart + 1, fallback.selectionStart + 1);
      fallback.focus();
      return;
    }
    insertAtCursor(fallback, text, back);
  }
  saveCode();
}

function insertPair(open, close) {
  if (targetIsInput()) { insertText(open); return; }
  if (usingCM) {
    const range = cmView.state.selection.main;
    const selected = cmView.state.sliceDoc(range.from, range.to);
    cmView.dispatch({
      changes: { from: range.from, to: range.to, insert: open + selected + close },
      selection: { anchor: range.from + 1, head: range.from + 1 + selected.length },
    });
    cmView.focus();
  } else {
    const start = fallback.selectionStart ?? 0;
    const end = fallback.selectionEnd ?? start;
    const selected = fallback.value.slice(start, end);
    fallback.setRangeText(open + selected + close, start, end, 'select');
    fallback.setSelectionRange(start + 1, start + 1 + selected.length);
    fallback.focus();
    fallback.dispatchEvent(new Event('input', { bubbles: true }));
  }
  saveCode();
}

function recordFallbackHistory() {
  const current = {
    value: fallback.value,
    start: fallback.selectionStart,
    end: fallback.selectionEnd,
  };
  const previous = fallbackHistory[fallbackHistoryIndex];
  if (previous?.value === current.value) {
    fallbackHistory[fallbackHistoryIndex] = current;
    return;
  }
  fallbackHistory = fallbackHistory.slice(0, fallbackHistoryIndex + 1);
  const now = Date.now();
  if (fallbackHistory.length > 1 && now - fallbackHistoryAt < 700) {
    fallbackHistory[fallbackHistory.length - 1] = current;
  } else {
    fallbackHistory.push(current);
    if (fallbackHistory.length > 200) fallbackHistory.shift();
  }
  fallbackHistoryIndex = fallbackHistory.length - 1;
  fallbackHistoryAt = now;
}

function stepFallbackHistory(delta) {
  const next = fallbackHistoryIndex + delta;
  if (next < 0 || next >= fallbackHistory.length) return false;
  fallbackHistoryIndex = next;
  const snapshot = fallbackHistory[next];
  fallback.value = snapshot.value;
  fallback.setSelectionRange(snapshot.start, snapshot.end);
  fallback.focus();
  saveCode();
  return true;
}

function opensPythonBlock(prefix) {
  let quote = '';
  let triple = false;
  let escaped = false;
  let depth = 0;
  for (let i = 0; i < prefix.length; i++) {
    const ch = prefix[i];
    if (quote) {
      if (escaped) { escaped = false; continue; }
      if (ch === '\\') { escaped = true; continue; }
      if (triple && prefix.slice(i, i + 3) === quote.repeat(3)) {
        quote = '';
        triple = false;
        i += 2;
      } else if (!triple && ch === quote) quote = '';
      continue;
    }
    if (ch === '#') break;
    if (ch === '"' || ch === "'") {
      quote = ch;
      triple = prefix.slice(i, i + 3) === ch.repeat(3);
      if (triple) i += 2;
    } else if ('([{'.includes(ch)) depth++;
    else if (')]}'.includes(ch)) depth = Math.max(0, depth - 1);
  }
  const code = prefix.trim();
  return depth === 0
    && /^(?:async\s+)?(?:if|elif|else|for|while|try|except|finally|with|def|class|match|case)\b/.test(code)
    && /:\s*(?:#.*)?$/.test(code);
}

// One of CodeMirror's own commands. Returns false when there is no editor, so
// the caller can fall back.
function editorCommand(name) {
  if (!usingCM || !cmCommands) {
    if (name === 'undo') return stepFallbackHistory(-1);
    if (name === 'redo') return stepFallbackHistory(1);
    return false;
  }
  const fn = cmCommands[name];
  if (typeof fn !== 'function') return false;
  fn(cmView);
  cmView.focus();
  saveCode();
  return true;
}

function indentFromToolbar() {
  if (targetIsInput()) { insertText('    '); return; }
  if (usingCM && !cmView.state.selection.main.empty && editorCommand('indentMore')) return;
  if (!usingCM && fallback.selectionStart !== fallback.selectionEnd) {
    editFallbackIndent(true);
    return;
  }
  insertText('    ');
}

// Take one indent level off, on every line the cursor or selection touches.
// Written here rather than using the editor's own indentLess, which would take
// off two spaces where the Tab button puts four.
function unindent() {
  if (!usingCM) { unindentFallback(); return; }
  const { state } = cmView;
  const changes = [];
  const seen = new Set();
  for (const range of state.selection.ranges) {
    const first = state.doc.lineAt(range.from).number;
    const last = state.doc.lineAt(range.to).number;
    for (let n = first; n <= last; n++) {
      if (seen.has(n)) continue;
      seen.add(n);
      const line = state.doc.line(n);
      const strip = line.text.match(/^\t|^ {1,4}/);
      if (strip) changes.push({ from: line.from, to: line.from + strip[0].length });
    }
  }
  if (!changes.length) return;
  cmView.dispatch({ changes });
  cmView.focus();
  saveCode();
}

// The same thing for the plain-textarea editor.
function unindentFallback() {
  editFallbackIndent(false);
}

// Apply or remove one four-space level on every touched line. Keep selections
// intact so toolbar indentation works the same as it does in CodeMirror.
function editFallbackIndent(add) {
  const el = fallback;
  const value = el.value;
  const start = el.selectionStart ?? 0;
  const end = el.selectionEnd ?? start;
  const first = value.lastIndexOf('\n', start - 1) + 1;
  const lastProbe = end > start && value[end - 1] === '\n' ? end - 1 : end;
  const edits = [];
  for (let lineStart = first; lineStart <= lastProbe;) {
    if (add) edits.push({ from: lineStart, to: lineStart, text: '    ' });
    else {
      const indent = value.slice(lineStart).match(/^(?:\t| {1,4})/);
      if (indent) edits.push({ from: lineStart, to: lineStart + indent[0].length, text: '' });
    }
    const newline = value.indexOf('\n', lineStart);
    if (newline < 0 || newline >= lastProbe) break;
    lineStart = newline + 1;
  }
  if (!edits.length) return;

  const mapOffset = (offset) => offset + edits.reduce((delta, edit) =>
    edit.from <= offset ? delta + edit.text.length - (edit.to - edit.from) : delta, 0);
  const nextStart = mapOffset(start);
  const nextEnd = mapOffset(end);
  let next = value;
  for (const edit of [...edits].reverse()) {
    next = next.slice(0, edit.from) + edit.text + next.slice(edit.to);
  }
  el.value = next;
  el.setSelectionRange(nextStart, nextEnd);
  el.focus();
  el.dispatchEvent(new Event('input', { bubbles: true }));
  saveCode();
}

function handleFallbackKeydown(e) {
  const el = fallback;
  const pairs = { '(': ')', '[': ']', '{': '}', '"': '"', "'": "'" };
  if ((e.ctrlKey || e.metaKey) && (e.key === 'z' || e.key === 'Z' || e.key === 'y' || e.key === 'Y')) {
    e.preventDefault();
    stepFallbackHistory(e.key.toLowerCase() === 'y' || e.shiftKey ? 1 : -1);
    return;
  }
  if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
    e.preventDefault();
    onRunClick();
    return;
  }
  if (e.key === 'Tab') {
    e.preventDefault();
    if (e.shiftKey) editFallbackIndent(false);
    else if (el.selectionStart !== el.selectionEnd) editFallbackIndent(true);
    else insertText('    ');
    return;
  }
  if (e.key === 'Enter') {
    e.preventDefault();
    const start = el.selectionStart ?? 0;
    const end = el.selectionEnd ?? start;
    const lineStart = el.value.lastIndexOf('\n', start - 1) + 1;
    const before = el.value.slice(lineStart, start);
    let indent = (before.match(/^[ \t]*/) || [''])[0];
    if (/^\s*(?:return\b|pass\b|break\b|continue\b|raise\b)/.test(before)) {
      indent = indent.replace(/\t| {1,4}$/, '');
    } else if (opensPythonBlock(before)) {
      indent += '    ';
    }
    el.setRangeText(`\n${indent}`, start, end, 'end');
    el.dispatchEvent(new Event('input', { bubbles: true }));
    return;
  }
  if (e.key === 'Backspace' && el.selectionStart === el.selectionEnd) {
    const pos = el.selectionStart;
    const lineStart = el.value.lastIndexOf('\n', pos - 1) + 1;
    const before = el.value.slice(lineStart, pos);
    const previous = el.value[pos - 1];
    if (pairs[previous] === el.value[pos]) {
      e.preventDefault();
      el.setRangeText('', pos - 1, pos + 1, 'end');
      el.dispatchEvent(new Event('input', { bubbles: true }));
      return;
    }
    if (/^(?:\t| )+$/.test(before)) {
      e.preventDefault();
      const remove = before.endsWith('\t') ? 1 : (before.length % 4 || Math.min(4, before.length));
      el.setRangeText('', pos - remove, pos, 'end');
      el.dispatchEvent(new Event('input', { bubbles: true }));
      return;
    }
  }
  const start = el.selectionStart ?? 0;
  const end = el.selectionEnd ?? start;
  if (!e.ctrlKey && !e.metaKey && !e.altKey) {
    if (start === end && Object.values(pairs).includes(e.key) && el.value[start] === e.key) {
      e.preventDefault();
      el.setSelectionRange(start + 1, start + 1);
    } else if (pairs[e.key]) {
      e.preventDefault();
      const selected = el.value.slice(start, end);
      el.setRangeText(e.key + selected + pairs[e.key], start, end, 'end');
      el.setSelectionRange(start + 1, start + 1 + selected.length);
      el.dispatchEvent(new Event('input', { bubbles: true }));
    }
  }
}

/* ------------------- shell history, and Ctrl+C ------------------------ */
// A phone keyboard has no arrow keys and no Ctrl+C, so the toolbar provides
// them. History is kept here rather than read back from the shell.
const shellHistory = [];
let shellAt = -1;

function shellRemember(line) {
  const t = line.trim();
  if (!t) return;
  if (shellHistory[shellHistory.length - 1] !== t) shellHistory.push(t);
  if (shellHistory.length > 100) shellHistory.shift();
  shellAt = -1;
}

function shellHistoryStep(delta) {
  if (!shellHistory.length) return;
  if (shellAt === -1) shellAt = shellHistory.length;
  shellAt = Math.max(0, Math.min(shellHistory.length, shellAt + delta));
  inputLine.value = shellAt >= shellHistory.length ? '' : shellHistory[shellAt];
  inputLine.dispatchEvent(new Event('input', { bubbles: true }));
  inputLine.focus();
}

// Map a keyboard key or character to its corresponding ASCII control code.
function charToControlCode(key) {
  if (!key || typeof key !== 'string') return null;
  if (key.length === 1) {
    const code = key.toUpperCase().charCodeAt(0);
    // ASCII '@' is 64 (\x00), 'A'-'Z' are 65-90 (\x01-\x1a)
    // '[' is 91 (\x1b = ESC), '\' is 92 (\x1c), ']' is 93 (\x1d), '^' is 94 (\x1e), '_' is 95 (\x1f)
    if (code >= 64 && code <= 95) {
      return String.fromCharCode(code - 64);
    }
    if (key === '?') return '\x7f'; // DEL
    if (key === '3') return '\x1b'; // ESC
    if (key === '4') return '\x1c';
    if (key === '5') return '\x1d';
    if (key === '6') return '\x1e';
    if (key === '7') return '\x1f';
    if (key === '8') return '\x7f';
  } else if (key === 'Backspace') {
    return '\x08';
  } else if (key === 'Enter') {
    return '\n';
  } else if (key === 'Tab') {
    return '\t';
  } else if (key === 'Escape') {
    return '\x1b';
  }
  return null;
}

// Send raw control characters to the active terminal (WebSocket on desktop, HTTP on mobile).
async function sendControlCode(str) {
  if (!str) return;

  // Send via WebSocket if open (pty xterm mode)
  if (termWs && termWs.readyState === WebSocket.OPEN) {
    sendTermInput(str);
    return;
  }

  // Otherwise send via HTTP input endpoint
  if (!runId) return;
  try {
    await fetch(`/api/runs/${runId}/input`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ data: str, raw: true }),
    });
  } catch { /* ignore */ }

  // In line-based console: give visual feedback
  if (!runIsPty || !isDesktop()) {
    const c = str.charCodeAt(0);
    if (c === 3) { // Ctrl+C
      appendOutput('^C\n', 'echo');
      inputLine.value = '';
      inputLine.style.height = '';
    } else if (c === 4) { // Ctrl+D
      appendOutput('^D\n', 'echo');
    } else if (c === 26) { // Ctrl+Z
      appendOutput('^Z\n', 'echo');
    } else if (c === 12) { // Ctrl+L (Clear screen)
      clearOutput();
    } else if (c === 21) { // Ctrl+U (Erase line)
      inputLine.value = '';
      inputLine.style.height = '';
    } else if (c === 23) { // Ctrl+W (Erase word)
      inputLine.value = inputLine.value.replace(/\S+\s*$/, '');
    } else if (c === 1) { // Ctrl+A (Beginning of line)
      inputLine.setSelectionRange(0, 0);
    } else if (c === 5) { // Ctrl+E (End of line)
      const len = inputLine.value.length;
      inputLine.setSelectionRange(len, len);
    }
  }
}

// A bare 0x03 and no newline: that is what makes the terminal driver raise
// SIGINT, instead of reading it as an empty line.
async function sendCtrlC() {
  return sendControlCode('\u0003');
}

// Ctrl modifier toggle (latching key for mobile virtual keyboard)
let isCtrlActive = false;

function setCtrlActive(on) {
  isCtrlActive = Boolean(on);
  const ctrlBtn = $('#ctrlBtn') || document.querySelector('[data-ctrl="mod"]');
  if (ctrlBtn) {
    ctrlBtn.classList.toggle('active', isCtrlActive);
    ctrlBtn.setAttribute('aria-pressed', isCtrlActive ? 'true' : 'false');
  }
  const consoleInput = $('#inputForm');
  if (consoleInput) {
    consoleInput.classList.toggle('ctrl-active', isCtrlActive);
  }
  if (isCtrlActive) {
    if (isDesktop() && term && !termMount.hidden) {
      try { term.focus(); } catch { /* ignore */ }
    } else {
      inputLine.focus({ preventScroll: true });
    }
  }
}

function toggleCtrlModifier() {
  setCtrlActive(!isCtrlActive);
}

$('#symbolbar').addEventListener('click', (e) => {
  const btn = e.target.closest('button');
  if (!btn || btn.hidden) return;
  e.preventDefault();
  if (btn.dataset.hist) { shellHistoryStep(btn.dataset.hist === 'up' ? -1 : 1); return; }
  if (btn.dataset.ctrl === 'mod' || btn.id === 'ctrlBtn') { toggleCtrlModifier(); return; }
  if (btn.dataset.ctrlKey) {
    const code = charToControlCode(btn.dataset.ctrlKey);
    if (code) sendControlCode(code);
    setCtrlActive(false);
    return;
  }
  if (btn.dataset.ctrl === 'c') { sendCtrlC(); setCtrlActive(false); return; }
  if (btn.dataset.key === 'tab') {
    if (mode === 'terminal') {
      sendControlCode('\t');
    } else {
      indentFromToolbar();
    }
    setCtrlActive(false);
    return;
  }
  if (btn.dataset.key === 'esc') {
    if (isCtrlActive) {
      setCtrlActive(false);
    } else {
      sendControlCode('\x1b');
    }
    return;
  }
  if (btn.dataset.key === 'untab') { unindent(); setCtrlActive(false); return; }
  if (btn.dataset.key === 'undo') { editorCommand('undo'); setCtrlActive(false); return; }
  if (btn.dataset.key === 'redo') { editorCommand('redo'); setCtrlActive(false); return; }
  if (btn.dataset.insert !== undefined) {
    if (isCtrlActive) {
      const val = btn.dataset.insert.trim();
      const ctrlChar = val ? charToControlCode(val[0]) : null;
      setCtrlActive(false);
      if (ctrlChar) {
        sendControlCode(ctrlChar);
        return;
      }
    }
    const pairs = { '(': ')', '[': ']', '{': '}', '"': '"', "'": "'" };
    const value = btn.dataset.insert;
    if (mode === 'script' && pairs[value]) insertPair(value, pairs[value]);
    else insertText(value, Number(btn.dataset.back || 0));
  }
});

/* --------------------------- console --------------------------------- */
// The console can take a lot of text in one burst, and appending each piece and
// scrolling on every one re-lays-out the whole block each time — on a phone that
// is what makes a chatty program look frozen while it runs. Collect a frame's
// worth and paint once.
const paintQueue = [];
let paintPending = null;

function clearOutput() {
  output.textContent = '';
  paintQueue.length = 0;
  outputEmpty = true;
}

function paintOutput() {
  paintPending = null;
  if (!paintQueue.length) return;
  // Follow the tail only if the reader is already there, so scrolling up to
  // read something is not undone by the next line.
  const atBottom = output.scrollHeight - output.scrollTop - output.clientHeight < 40;
  const frag = document.createDocumentFragment();
  for (const node of paintQueue) frag.appendChild(node);
  paintQueue.length = 0;
  output.appendChild(frag);
  // Cap rendered nodes so prolonged terminal sessions do not freeze mobile browser layout
  while (output.childNodes.length > 2500) {
    output.removeChild(output.firstChild);
  }
  if (atBottom) output.scrollTop = output.scrollHeight;
}

function queuePaint(node) {
  paintQueue.push(node);
  if (paintPending === null) paintPending = requestAnimationFrame(paintOutput);
}

function appendOutput(text, cls) {
  // A command that is quietly working looks exactly like one that has stopped.
  // Remember when we last heard anything, so the note below can speak up.
  if (cls !== 'muted') { lastOutputAt = Date.now(); quietNoted = false; }
  if (outputEmpty) { output.textContent = ''; outputEmpty = false; }
  if (cls === 'err' || cls === 'muted') {
    const d = document.createElement('div');
    d.className = cls;
    d.textContent = text;
    queuePaint(d);
  } else if (cls === 'echo') {
    const s = document.createElement('span');
    s.className = 'echo';
    s.textContent = text;
    queuePaint(s);
  } else {
    queuePaint(document.createTextNode(text));
  }
}
function setStatus(kind, text) {
  statusEl.className = `status${kind ? ' ' + kind : ''}`;
  statusEl.textContent = text;
}

function setRunning(on) {
  runBtn.classList.toggle('stopping', on);
  runLabel.textContent = on ? 'Stop' : 'Run';
  runIcon.textContent = on ? '■' : '▶';
  inputLine.disabled = !on;
  sendBtn.disabled = !on;
  inputRow.classList.toggle('active', on);
  if (!on) {
    inputLine.value = '';
    inputLine.style.height = '';
    setCtrlActive(false);
  }
}

function onRunClick() {
  if (runId) stopRun();
  else startRun();
}

// If the pre-fill box somehow holds the program itself (for example stale data
// left over from an older version), sending it as stdin is never what you want.
function looksLikePastedCode(code, prefill) {
  const codeLines = code.split('\n').map((l) => l.trim()).filter(Boolean);
  const preLines = prefill.split('\n').map((l) => l.trim()).filter(Boolean);
  if (!preLines.length) return false;
  return preLines.every((l) => codeLines.includes(l));
}

async function snapshotFiles() {
  try {
    const r = await fetch('/api/files');
    const d = await r.json();
    return new Set((d.files || []).map((f) => f.name));
  } catch {
    return null;
  }
}

async function startRun() {
  switchTab('console');
  clearOutput();

  // On a wide screen the Terminal and REPL get a real terminal emulator.
  if (isDesktop() && (mode === 'terminal' || mode === 'repl')) {
    if (await startPtyTerminal(mode)) return;
  }
  teardownTerminal();

  setRunning(false);
  setStatus('running', 'Starting…');
  runBtn.disabled = true;

  const code = getCode();
  let prefill = mode === 'script' ? stdinEl.value : '';

  if (mode === 'script' && prefill.trim() && looksLikePastedCode(code, prefill)) {
    prefill = '';
    stdinEl.value = '';
    try { localStorage.removeItem(STORAGE_STDIN); } catch { /* ignore */ }
    updatePrefillUI();
    appendOutput('⚠ The Pre-fill input box held your program code, so it was not sent.\n', 'muted');
  } else if (mode === 'script' && prefill.trim()) {
    for (const line of prefill.split('\n')) appendOutput(line + '\n', 'echo');
  }

  if (mode === 'repl') appendOutput('Python REPL — type an expression and press Enter.\n', 'muted');
  if (mode === 'terminal') appendOutput('Terminal — type a shell command and press Enter.\n', 'muted');

  // Remember what is already in the space, so we can tell you about new files.
  filesAtStart = mode === 'script' ? await snapshotFiles() : null;

  if (!window.EventSource) return startRunLegacy(code, prefill);

  let data;
  try {
    const res = await fetch('/api/runs', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ code, stdin: prefill, mode }),
    });
    data = await res.json();
    if (!res.ok || !data.runId) {
      appendOutput(data.error || 'Could not start the run.', 'err');
      setStatus('error', 'Not started');
      runBtn.disabled = false;
      return;
    }
  } catch (err) {
    appendOutput('Network error: ' + err.message, 'err');
    setStatus('error', 'Request failed');
    runBtn.disabled = false;
    return;
  }

  runId = data.runId;
  runIsPty = Boolean(data.pty);
  runStderr = '';
  runBtn.disabled = false;
  setRunning(true);
  if (mode === 'repl') setStatus('running', 'REPL ready — type below and press Enter');
  else if (mode === 'terminal') setStatus('running', 'Terminal ready — type below and press Enter');
  else setStatus('running', 'Running…');
  openStream(runId);
  if (mode !== 'script') inputLine.focus();
}

function openStream(id) {
  receivedEvents = false;
  lastRunEventId = 0;
  es = new EventSource(`/api/runs/${id}/events`);
  es.onmessage = (ev) => {
    let e;
    try { e = JSON.parse(ev.data); } catch { return; }
    // EventSource reconnects on a dropped connection and sends Last-Event-ID.
    // Runs replay their history, so ignore anything the page already rendered.
    if (Number.isFinite(e.id)) {
      if (e.id <= lastRunEventId) return;
      lastRunEventId = e.id;
    }
    receivedEvents = true;
    if (e.type === 'output') {
      if (e.stream === 'stderr') runStderr += e.text;
      appendOutput(e.text, e.stream === 'stderr' ? 'err' : null);
    } else if (e.type === 'exit') {
      finishRun(e);
    }
  };
  es.onerror = async () => {
    // EventSource retries while CONNECTING. Keep it alive so a transient
    // mobile-network drop does not turn an active run into an error.
    if (es && es.readyState === EventSource.CONNECTING) return;
    // If the stream is permanently closed, use the result endpoint as fallback.
    if (es) { es.close(); es = null; }
    const id2 = runId;
    if (!id2) return;
    if (!receivedEvents) {
      try {
        const r = await fetch(`/api/runs/${id2}`);
        if (r.ok) {
          const d = await r.json();
          if (d.stdout) appendOutput(d.stdout, null);
          if (d.stderr) appendOutput(d.stderr, 'err');
          finishRun({ status: d.status || 'error', exit_code: d.exit_code, elapsed_ms: d.elapsed_ms, truncated: d.truncated });
          return;
        }
      } catch { /* fall through */ }
    }
    finishRun({ status: 'error', exit_code: null, elapsed_ms: 0, truncated: false });
  };
}

function finishRun(e) {
  if (es) { es.close(); es = null; }
  runId = null;
  setRunning(false);
  reportNewFiles();
  const t = e.elapsed_ms ? ` · ${(e.elapsed_ms / 1000).toFixed(2)}s` : '';
  if (e.status === 'success') {
    setStatus('success', `✓ Done${t} · exit ${e.exit_code ?? 0}`);
    if (outputEmpty && mode === 'script') {
      appendOutput('✓ Program completed with no output (exit code 0).\n💡 Tip: Did you forget print(...) ? In Script mode, use print(value) to show output.\n', 'muted');
    }
  }
  else if (e.status === 'idle_timeout') setStatus('timeout', `⏱ Stopped: no activity${t}`);
  else if (e.status === 'timeout') setStatus('timeout', `⏱ Time limit reached${t}`);
  else if (e.status === 'output_limit') setStatus('error', `✗ Stopped: too much output${t}`);
  else if (e.status === 'killed') setStatus('error', `■ Stopped${t}`);
  else setStatus('error', `✗ Error${t} · exit ${e.exit_code ?? '?'}`);
  if (e.truncated) appendOutput('\n… output truncated.', 'muted');
  if (e.status === 'error' || e.status === 'output_limit') explainError(runStderr);
}

// After a run, say so if the program saved anything — otherwise it is easy to
// think nothing happened.
function reportNewFiles() {
  const before = filesAtStart;
  filesAtStart = null;
  if (!before) return;
  snapshotFiles().then((now) => {
    if (!now) return;
    const added = [...now].filter((n) => !before.has(n) && !n.split('/').pop().startsWith('.'));
    if (added.length) {
      appendOutput(`\n📄 saved in your space: ${added.join(', ')} — tap Files to open\n`, 'muted');
    }
  });
}

async function stopRun() {
  if (!runId) return;
  setStatus('running', 'Stopping…');
  try { await fetch(`/api/runs/${runId}/kill`, { method: 'POST' }); } catch { /* ignore */ }
}

// Drop any live session. Switching mode must never leave the old session
// quietly receiving keystrokes — that is how a Terminal session ends up
// looking like a REPL (or the other way round).
function resetRun() {
  if (runId) {
    try { fetch(`/api/runs/${runId}/kill`, { method: 'POST' }); } catch { /* ignore */ }
  }
  if (es) { try { es.close(); } catch { /* ignore */ } es = null; }
  if (termWs) { try { termWs.close(); } catch { /* ignore */ } termWs = null; }
  runId = null;
  termRunId = null;
  runIsPty = false;
  receivedEvents = false;
  setRunning(false);
  setCtrlActive(false);
  setStatus('', '');
}

// Fallback for browsers without EventSource: one-shot run.
async function startRunLegacy(code, prefill) {
  try {
    const res = await fetch('/api/run', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ code, stdin: prefill }),
    });
    const d = await res.json();
    if (d.stdout) appendOutput(d.stdout, null);
    if (d.stderr) appendOutput(d.stderr, 'err');
    if (!d.stdout && !d.stderr) appendOutput(d.error || '(no output)', d.error ? 'err' : 'muted');
    const t = d.execution_time ? ` · ${d.execution_time}` : '';
    setStatus(d.status === 'success' ? 'success' : 'error',
      `${d.status === 'success' ? '✓ Done' : '✗ ' + (d.status || 'error')}${t}`);
  } catch (err) {
    appendOutput('Network error: ' + err.message, 'err');
    setStatus('error', 'Request failed');
  } finally {
    runBtn.disabled = false;
  }
}

/* input line */
// Enter sends; the box grows as you type so a long command is readable.
inputLine.addEventListener('keydown', (e) => {
  // Physical Ctrl key combinations (when mode is terminal or repl)
  if ((e.ctrlKey || e.metaKey) && !e.altKey) {
    const key = e.key.toLowerCase();
    const hasSelection = inputLine.selectionStart !== inputLine.selectionEnd;
    // Allow standard browser copy/paste/select-all if user explicitly selected text
    if (hasSelection && (key === 'c' || key === 'a')) {
      return;
    }
    if (key === 'v') {
      return; // allow paste
    }
    if (mode === 'terminal' || mode === 'repl') {
      const ctrlChar = charToControlCode(e.key);
      if (ctrlChar) {
        e.preventDefault();
        sendControlCode(ctrlChar);
        if (isCtrlActive) setCtrlActive(false);
        return;
      }
    }
  }

  // Virtual Ctrl modifier active (toggled from toolbar button)
  if (isCtrlActive) {
    if (['Control', 'Shift', 'Alt', 'Meta'].includes(e.key)) return;
    if (e.key === 'Unidentified' || e.keyCode === 229) {
      // Android software keyboard (IME) in progress: wait for beforeinput / input
      return;
    }
    if (e.key === 'Escape') {
      e.preventDefault();
      setCtrlActive(false);
      return;
    }
    const ctrlChar = charToControlCode(e.key);
    if (ctrlChar) {
      e.preventDefault();
      e.stopPropagation();
      setCtrlActive(false);
      sendControlCode(ctrlChar);
      return;
    }
    return;
  }

  if (e.key === 'Enter' && !e.shiftKey) {
    e.preventDefault();
    if (typeof inputForm.requestSubmit === 'function') inputForm.requestSubmit();
    else inputForm.dispatchEvent(new Event('submit', { cancelable: true }));
  }
});

// Mobile virtual keyboards (Android Chrome) often send characters via beforeinput
inputLine.addEventListener('beforeinput', (e) => {
  if (isCtrlActive && e.data) {
    e.preventDefault();
    e.stopPropagation();
    const ctrlChar = charToControlCode(e.data[0]);
    setCtrlActive(false);
    if (ctrlChar) {
      sendControlCode(ctrlChar);
    }
  }
});

inputLine.addEventListener('input', (e) => {
  if (isCtrlActive) {
    const rawChar = e.data || (inputLine.value ? inputLine.value.slice(-1) : '');
    if (rawChar) {
      const char = rawChar[0];
      const ctrlChar = charToControlCode(char);
      if (inputLine.value.endsWith(rawChar)) {
        inputLine.value = inputLine.value.slice(0, -rawChar.length);
      } else if (inputLine.value.endsWith(char)) {
        inputLine.value = inputLine.value.slice(0, -1);
      }
      setCtrlActive(false);
      if (ctrlChar) {
        sendControlCode(ctrlChar);
        return;
      }
    }
  }
  inputLine.style.height = 'auto';
  inputLine.style.height = `${Math.min(inputLine.scrollHeight, 110)}px`;
});

// Global key interceptor when Ctrl modifier is active and focus is outside inputLine
window.addEventListener('keydown', (e) => {
  if (isCtrlActive && e.target !== inputLine) {
    if (['Control', 'Shift', 'Alt', 'Meta'].includes(e.key)) return;
    if (e.key === 'Unidentified' || e.keyCode === 229) return;
    if (e.key === 'Escape') {
      e.preventDefault();
      setCtrlActive(false);
      return;
    }
    const ctrlChar = charToControlCode(e.key);
    if (ctrlChar) {
      e.preventDefault();
      e.stopPropagation();
      setCtrlActive(false);
      sendControlCode(ctrlChar);
    }
  }
}, true);

inputForm.addEventListener('submit', async (e) => {
  e.preventDefault();
  if (!runId) return;
  const value = inputLine.value;
  inputLine.value = '';
  inputLine.style.height = '';
  if (mode === 'terminal' || mode === 'repl') shellRemember(value);
  // A pseudoterminal echoes what you type by itself, so our own echo would
  // double every line. The line-based runs have no echo of their own.
  if (!runIsPty) appendOutput((mode === 'terminal' ? '$ ' : '') + value + '\n', 'echo');
  try {
    await fetch(`/api/runs/${runId}/input`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ data: value }),
    });
  } catch { /* ignore */ }
  inputLine.focus();
});

runBtn.addEventListener('click', onRunClick);

/* --------------------------- save as .py ----------------------------- */
// Entirely client side: the code is wrapped in a Blob and handed straight to
// the browser, so nothing is uploaded anywhere. The click handler stays
// synchronous on purpose — iOS Safari only allows a download that starts inside
// the same user gesture, so there is no await before downloadPython().
const STORAGE_FILENAME = 'pypad-file-name';

try {
  const remembered = localStorage.getItem(STORAGE_FILENAME);
  if (remembered) fileNameInput.value = remembered;
} catch { /* private mode, ignore */ }

function rememberName(name) {
  fileNameInput.value = name;
  try { localStorage.setItem(STORAGE_FILENAME, name); } catch { /* ignore */ }
}

// Tidy the name up as soon as the field loses focus, so what you see is what
// gets saved.
fileNameInput.addEventListener('change', () => rememberName(pythonFilename(fileNameInput.value)));
fileNameInput.addEventListener('blur', () => rememberName(pythonFilename(fileNameInput.value)));

function saveCodeAsPy() {
  const name = pythonFilename(fileNameInput.value);
  rememberName(name);
  const code = getCode();
  const { bytes } = downloadPython(code, name);
  setStatus('success', `✓ Saved ${name} · ${bytes} bytes`);
}

downloadBtn.addEventListener('click', saveCodeAsPy);

/* ---- and the other ways out, for devices that refuse a download ---- */
function saveSay(text) {
  saveOut.hidden = false;
  saveOut.textContent = text;
}

function openSaveDialog() {
  saveOut.hidden = true;
  saveOut.textContent = '';
  // Only offered where it actually exists, so it is never a dead button.
  saveShare.hidden = !canShareFiles();
  if (typeof saveDialog.showModal === 'function') saveDialog.showModal();
  else saveDialog.setAttribute('open', '');
}

saveMoreBtn.addEventListener('click', openSaveDialog);

saveDownload.addEventListener('click', () => {
  const name = pythonFilename(fileNameInput.value);
  rememberName(name);
  const { bytes } = downloadPython(getCode(), name);
  saveSay(`Asked the browser to save ${name} (${bytes} bytes).\n\nIf nothing appeared, your browser is refusing downloads — use Share or Copy below.`);
});

saveShare.addEventListener('click', async () => {
  const name = pythonFilename(fileNameInput.value);
  rememberName(name);
  try {
    const { filename } = await sharePython(getCode(), name);
    saveSay(`Shared ${filename}.`);
  } catch (err) {
    saveSay(`Could not share: ${err.message}\n\nUse Copy instead.`);
  }
});

// The same file, but fetched from the server with Content-Disposition: the
// browser's own download manager handles it, which is the path that keeps
// working on Android when a blob download is refused. It also leaves the file
// in your workspace, so it shows up under Files.
saveServer.addEventListener('click', async () => {
  const name = pythonFilename(fileNameInput.value);
  rememberName(name);
  saveSay(`Saving ${name} on the server…`);
  try {
    const blob = new Blob([getCode()], { type: 'text/x-python;charset=utf-8' });
    const res = await fetch(`/api/files?name=${encodeURIComponent(name)}`, { method: 'POST', body: blob });
    const d = await res.json();
    if (!d.ok) {
      saveSay(`✗ ${d.error || 'the server refused the file'}`);
      return;
    }
    const a = document.createElement('a');
    a.href = `/api/files/${encodeURIComponent(name)}`;
    a.download = name;
    a.style.display = 'none';
    document.body.appendChild(a);
    a.click();
    setTimeout(() => a.remove(), 1000);
    saveSay(`✓ ${name} is in your workspace, and the browser has been asked to download it.\n\nIt is also listed under Files.`);
  } catch (err) {
    saveSay(`Could not reach the server: ${err.message}`);
  }
});

saveCopy.addEventListener('click', async () => {
  try {
    await copyText(getCode());
    saveSay('✓ Copied. Paste it wherever you like.');
  } catch (err) {
    saveSay(`Could not copy: ${err.message}`);
  }
});

// Ctrl/Cmd+S in the editor saves instead of opening the browser's own dialog.
window.addEventListener('keydown', (e) => {
  if ((e.ctrlKey || e.metaKey) && (e.key === 's' || e.key === 'S')) {
    e.preventDefault();
    saveCodeAsPy();
  }
});

clearBtn.addEventListener('click', () => {
  clearOutput();
  const s = document.createElement('span');
  s.className = 'muted';
  s.textContent = 'Press ▶ Run to execute your code.';
  output.appendChild(s);
  setStatus('', '');
});

/* ----------------------------- boot ---------------------------------- */
function updatePrefillUI() {
  const lines = stdinEl.value.split('\n').filter((l) => l.trim()).length;
  prefillCount.textContent = lines ? `${lines} line${lines > 1 ? 's' : ''}` : '';
  if (lines) prefillDetails.open = true;
}

stdinEl.value = loadStored(STORAGE_STDIN, '');
stdinEl.addEventListener('input', () => {
  try { localStorage.setItem(STORAGE_STDIN, stdinEl.value); } catch { /* ignore */ }
  updatePrefillUI();
});
prefillClear.addEventListener('click', () => {
  stdinEl.value = '';
  try { localStorage.removeItem(STORAGE_STDIN); } catch { /* ignore */ }
  updatePrefillUI();
});
updatePrefillUI();
initEditor();

/* --------------------------- modes ----------------------------------- */
function setMode(next) {
  if (mode === next) return;
  mode = next;
  document.querySelectorAll('.modebar .mode').forEach((b) => b.classList.toggle('active', b.dataset.mode === next));
  document.querySelector('.console-input .prompt').textContent = next === 'terminal' ? '$' : '›';
  prefillDetails.hidden = next !== 'script';
  // The editor belongs to Script mode. Hiding it in REPL/Terminal removes any
  // doubt about where to type.
  editorPanel.hidden = next !== 'script';
  codeTab.hidden = next !== 'script';
  switchTab('console');
  if (next === 'script' && usingCM) setTimeout(() => cmView.requestMeasure(), 0);
  resetRun();
  clearOutput();
  // The toolbar changes with the mode: shell keys in the terminal, code tools
  // in Script and REPL.
  const set = next === 'terminal' ? 'shell' : 'code';
  document.querySelectorAll('#symbolbar .sym-set').forEach((s) => { s.hidden = s.dataset.set !== set; });
  document.querySelectorAll('#symbolbar [data-only="script"]').forEach((b) => { b.hidden = next !== 'script'; });
  const hint = next === 'script' ? 'Press ▶ Run to execute your code.'
    : next === 'repl' ? 'Press ▶ Run to start a Python REPL, then type below.'
      : 'Press ▶ Run to open a terminal, then type commands below.';
  appendOutput(hint, 'muted');
  setStatus('', '');
}
modebar.addEventListener('click', (e) => {
  const b = e.target.closest('.mode');
  if (b && !b.hidden) setMode(b.dataset.mode);
});

/* ------------------------- packages dialog --------------------------- */
async function openPackages() {
  pkgOut.hidden = true;
  pkgOut.textContent = '';
  if (typeof pkgDialog.showModal === 'function') pkgDialog.showModal();
  else pkgDialog.setAttribute('open', '');
  try {
    const res = await fetch('/api/packages');
    const d = await res.json();
    pkgAllowed.textContent = '';
    (d.allowlist || []).forEach((name) => {
      const c = document.createElement('button');
      c.type = 'button';
      c.className = 'chip';
      c.textContent = name;
      c.addEventListener('click', () => { pkgInput.value = name; pkgInput.focus(); });
      pkgAllowed.appendChild(c);
    });
  } catch { /* ignore */ }
  loadInstalled();
}

// What is in the venv right now, each with a way to take it back out.
async function loadInstalled() {
  pkgInstalled.textContent = '';
  try {
    const res = await fetch('/api/packages/installed');
    const d = await res.json();
    const list = d.packages || [];
    if (!list.length) {
      pkgInstalled.textContent = 'Nothing installed yet.';
      return;
    }
    list.forEach((p) => {
      const b = document.createElement('button');
      b.type = 'button';
      b.className = 'chip';
      b.textContent = `${p.name} ✕`;
      b.title = `Remove ${p.name}${p.version ? ` ${p.version}` : ''}`;
      b.addEventListener('click', () => removePackage(p.name, b));
      pkgInstalled.appendChild(b);
    });
  } catch {
    pkgInstalled.textContent = 'Could not read the list.';
  }
}

async function removePackage(name, btn) {
  if (!window.confirm(`Remove ${name} from the server?`)) return;
  btn.disabled = true;
  pkgOut.hidden = false;
  pkgOut.textContent = `Removing ${name}…`;
  try {
    const res = await fetch('/api/packages/uninstall', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ name }),
    });
    const d = await res.json();
    pkgOut.textContent = (d.ok ? `✓ ${name} removed.\n\n` : `✗ ${d.error || 'failed'}\n\n`) + (d.output || '');
  } catch (err) {
    pkgOut.textContent = 'Network error: ' + err.message;
  } finally {
    btn.disabled = false;
    loadInstalled();
  }
}
async function installPackage() {
  const name = pkgInput.value.trim();
  if (!name) return;
  pkgInstall.disabled = true;
  pkgOut.hidden = false;
  pkgOut.textContent = `Installing ${name}…`;
  try {
    const res = await fetch('/api/packages', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ name }),
    });
    const d = await res.json();
    pkgOut.textContent = (d.ok ? `✓ ${name} installed.\n\n` : `✗ ${d.error || 'failed'}\n\n`) + (d.output || '');
    if (d.ok) loadInstalled();
  } catch (err) {
    pkgOut.textContent = 'Network error: ' + err.message;
  } finally {
    pkgInstall.disabled = false;
  }
}
pkgBtn.addEventListener('click', openPackages);
pkgInstall.addEventListener('click', installPackage);
pkgInput.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); installPackage(); } });

/* --------------------------- workspace files ------------------------- */
function fmtSize(n) {
  if (n < 1024) return `${n} B`;
  if (n < 1024 * 1024) return `${(n / 1024).toFixed(1)} KB`;
  if (n < 1024 * 1024 * 1024) return `${(n / 1024 / 1024).toFixed(1)} MB`;
  return `${(n / 1024 / 1024 / 1024).toFixed(2)} GB`;
}

async function loadFiles() {
  fileList.textContent = '';
  try {
    const res = await fetch('/api/files');
    const d = await res.json();
    if (!d.files || !d.files.length) {
      const p = document.createElement('div');
      p.className = 'muted';
      p.textContent = 'No files yet. Upload one above, or run a program that writes one.';
      fileList.appendChild(p);
      return;
    }
    d.files.forEach((f) => {
      const row = document.createElement('div');
      row.className = 'file-row';
      const a = document.createElement('a');
      a.className = 'file-name';
      a.href = `/api/files/${encodeURIComponent(f.name)}`;
      a.setAttribute('download', '');
      a.textContent = f.name;
      const size = document.createElement('span');
      size.className = 'file-size';
      size.textContent = fmtSize(f.size);

      const open = document.createElement('button');
      open.type = 'button';
      open.className = 'mini-btn';
      open.textContent = 'Open';
      open.title = 'Open this file in the editor';
      open.addEventListener('click', () => openInEditor(f));

      const ren = document.createElement('button');
      ren.type = 'button';
      ren.className = 'mini-btn';
      ren.textContent = 'Rename';
      ren.addEventListener('click', () => startRename(f, row));

      const del = document.createElement('button');
      del.type = 'button';
      del.className = 'mini-btn';
      del.textContent = 'Delete';
      del.addEventListener('click', async () => {
        await fetch(`/api/files/${encodeURIComponent(f.name)}`, { method: 'DELETE' }).catch(() => {});
        loadFiles();
      });
      row.append(a, size, open, ren, del);
      fileList.appendChild(row);
    });
    const total = document.createElement('div');
    total.className = 'file-total';
    total.textContent = `${d.files.length} file(s) · ${fmtSize(d.total)} of ${fmtSize(d.limit)} used · this space is yours alone and clears after ~${spaceTtlHours}h idle`;
    fileList.appendChild(total);
  } catch {
    /* ignore */
  }
}

/* --------------------- opening a file in the editor ------------------- */
// Files and the editor belong together: open one here, edit it, and Save .py
// writes it back to the workspace under the name in the box.
const MAX_OPEN_BYTES = 512 * 1024;

function fileSay(text, bad) {
  fileOut.hidden = false;
  fileOut.className = bad ? 'pkg-out err' : 'pkg-out ok';
  fileOut.textContent = text;
}

async function openInEditor(f) {
  if (f.size > MAX_OPEN_BYTES) {
    fileSay(`${f.name} is ${fmtSize(f.size)} — too big to open here. Download it instead.`, true);
    return;
  }
  try {
    const res = await fetch(`/api/files/${encodeURIComponent(f.name)}`);
    if (!res.ok) throw new Error(`the server answered ${res.status}`);
    const text = await res.text();
    if (/\u0000/.test(text.slice(0, 4000))) {
      fileSay(`${f.name} does not look like a text file. Download it instead.`, true);
      return;
    }
    setCode(text);
    fileNameInput.value = f.name;
    rememberName(f.name);
    filesDialog.close();
    // The editor only exists in Script mode, and the tab is called "editor".
    // Opening a file from Terminal or REPL used to switch to a tab that does not
    // exist, which hid both panels and left the reader looking at a blank screen.
    if (mode !== 'script') setMode('script');
    switchTab('editor');
    setStatus('success', `Opened ${f.name}. Edit it, then Save .py to write it back.`);
  } catch (err) {
    fileSay(`Could not open ${f.name}: ${err.message}`, true);
  }
}

// Rename in place, in the row itself — a system prompt would be clumsier on a
// phone and is blocked in some webviews.
function startRename(f, row) {
  const input = document.createElement('input');
  input.type = 'text';
  input.className = 'file-rename';
  input.value = f.name;
  input.setAttribute('aria-label', `New name for ${f.name}`);
  row.textContent = '';
  row.appendChild(input);
  input.focus();
  input.select();

  let done = false;
  const finish = async (commit) => {
    if (done) return;
    done = true;
    const to = input.value.trim();
    if (!commit || !to || to === f.name) { loadFiles(); return; }
    try {
      const res = await fetch('/api/files/rename', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ from: f.name, to }),
      });
      const d = await res.json();
      if (!d.ok) fileSay(d.error || 'Could not rename it.', true);
    } catch (err) {
      fileSay(`Could not rename it: ${err.message}`, true);
    }
    loadFiles();
  };
  input.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') { e.preventDefault(); finish(true); }
    if (e.key === 'Escape') { e.preventDefault(); finish(false); }
  });
  input.addEventListener('blur', () => finish(true));
}

/* ------------------- explaining what went wrong ----------------------- */
// A traceback is accurate but hard to read, and its line numbers point at a
// temporary file. Turn the common ones into one plain sentence, and offer to
// jump to the line in the editor.
const ERROR_HINTS = [
  [/IndentationError: unexpected indent/, 'this line is indented further than the block it belongs to — line it up with the lines above'],
  [/IndentationError: expected an indented block/, 'the line after a colon (:) has to be indented — press ⇥ Tab on it'],
  [/TabError/, 'indentation is mixed: some lines use spaces and some use tabs. Make them all spaces'],
  [/SyntaxError/, 'Python could not read this line — something is missing or extra, such as a bracket, a quote, or the colon at the end of an if/for/while line'],
  [/NameError: name '([^']+)' is not defined/, (m) => `there is nothing called ${m[1]} yet — check the spelling, or create it before this line`],
  [/TypeError: can only concatenate str/, 'text and a number cannot be joined with + — wrap the number in str(…), or use an f-string'],
  [/TypeError: unsupported operand type/, 'these two values cannot be combined with that operator — often a number and a piece of text'],
  [/ValueError: invalid literal for int\(\) with base 10: '([^']*)'/, (m) => `int() was given ${JSON.stringify(m[1])}, which is not a whole number — use input() for text, int(input()) only for digits`],
  [/ZeroDivisionError/, 'something was divided by zero'],
  [/IndexError: list index out of range/, 'that position is past the end of the list — remember the first item is 0'],
  [/KeyError: (.+)/, (m) => `that key is not in the dictionary: ${m[1]}`],
  [/FileNotFoundError/, 'that file is not in the workspace — check the name under Files'],
  [/ModuleNotFoundError: No module named '([^']+)'/, (m) => `${m[1]} is not installed — open Packages and add it`],
  [/RecursionError/, 'a function keeps calling itself and never stops'],
  [/json\.decoder\.JSONDecodeError|JSONDecodeError/, 'that text is not valid JSON — look for a missing quote, comma or brace'],
  [/ValueError: time data .* does not match format/, 'the date does not match the format you gave it — check the %Y-%m-%d style pattern against the text'],
  [/urllib\.error\.HTTPError: HTTP Error 403/, 'the site answered 403 Forbidden — it refused the request. Some sites turn away anything that does not look like a browser'],
  [/urllib\.error\.HTTPError: HTTP Error 404/, 'the site answered 404 Not Found — there is nothing at that address'],
  [/urllib\.error\.HTTPError: HTTP Error (\d+)/, (m) => `the site answered HTTP ${m[1]} — the request reached it, but it refused`],
  [/URLError: <urlopen error timed out>/, 'the site did not answer in time — it may be slow, or blocked'],
  [/URLError: <urlopen error \[Errno -2\]/, 'that address could not be looked up — check the spelling'],
  [/URLError: <urlopen error \[Errno -3\]/, 'that address could not be looked up right now — the name service did not answer'],
  [/urllib\.error\.URLError: (.+)/, (m) => `the address could not be reached: ${m[1]}`],
  [/SSLError/, 'the secure connection could not be set up'],
];

// A traceback carries a frame for every call on the way down, and most of them
// are inside Python itself — a call to urllib can end with the reader being
// offered line 611 of request.py, a file they cannot see. The line worth
// offering is the last one in their own file.
function isLibraryFrame(file) {
  return /\/python\d+(\.\d+)?\//.test(file) || file.includes('site-packages') || file.includes('/lib/python');
}

function userFrameLine(text) {
  const frames = [...text.matchAll(/File "([^"]+)", line (\d+)/g)]
    .map((m) => ({ file: m[1], line: Number(m[2]) }));
  if (!frames.length) return null;
  const own = frames.filter((f) => !isLibraryFrame(f.file));
  if (!own.length) return null;
  return own[own.length - 1].line;
}

function explainError(text) {
  if (!text) return;
  const line = userFrameLine(text);
  let hint = null;
  for (const [re, msg] of ERROR_HINTS) {
    const m = text.match(re);
    if (m) { hint = typeof msg === 'function' ? msg(m) : msg; break; }
  }
  if (!hint && !line) return;

  const box = document.createElement('div');
  box.className = 'err-help';
  const label = document.createElement('span');
  label.textContent = line ? `Line ${line}: ${hint || 'look at the message above.'}` : hint;
  box.appendChild(label);
  if (line) {
    const go = document.createElement('button');
    go.type = 'button';
    go.className = 'mini-btn';
    go.textContent = `Go to line ${line}`;
    go.addEventListener('click', () => gotoLine(line));
    box.appendChild(go);
  }
  paintOutput(); // release anything still queued, so the note lands below it
  output.appendChild(box);
  output.scrollTop = output.scrollHeight;
}
// Put the cursor on a line of the editor, switching to it if we are elsewhere.
function gotoLine(n) {
  if (mode !== 'script') setMode('script');
  switchTab('editor');
  const count = getCode().split('\n').length;
  const want = Math.max(1, Math.min(n, count));
  if (usingCM) {
    const line = cmView.state.doc.line(want);
    cmView.dispatch({ selection: { anchor: line.from }, scrollIntoView: true });
    cmView.focus();
  } else {
    let pos = 0;
    for (let i = 1; i < want; i++) {
      const next = fallback.value.indexOf('\n', pos);
      if (next === -1) break;
      pos = next + 1;
    }
    fallback.focus();
    fallback.setSelectionRange(pos, pos);
  }
}

async function openFiles() {
  fileOut.hidden = true;
  fileOut.textContent = '';
  if (typeof filesDialog.showModal === 'function') filesDialog.showModal();
  else filesDialog.setAttribute('open', '');
  loadFiles();
}

async function uploadFiles() {
  const files = Array.from(fileInput.files || []);
  if (!files.length) return;
  uploadBtn.disabled = true;
  fileOut.hidden = false;
  const lines = [];
  for (const f of files) {
    try {
      const res = await fetch(`/api/files?name=${encodeURIComponent(f.name)}`, { method: 'POST', body: f });
      const d = await res.json();
      lines.push(`${d.ok ? '✓' : '✗'} ${f.name}${d.ok ? ` (${fmtSize(d.size || 0)})` : ` — ${d.error || 'failed'}`}`);
    } catch (err) {
      lines.push(`✗ ${f.name} — ${err.message}`);
    }
  }
  fileOut.textContent = lines.join('\n');
  fileInput.value = '';
  uploadBtn.disabled = false;
  loadFiles();
}

filesBtn.addEventListener('click', openFiles);
uploadBtn.addEventListener('click', uploadFiles);

/* -------------------- where the input line sits ----------------------- */
// On a phone the keyboard covers the bottom of the screen, so let the input
// sit above the output instead. The choice is remembered.
let inputOnTop = false;
try { inputOnTop = localStorage.getItem('mobi-py-input-top') === '1'; } catch { /* ignore */ }
function applyInputPos() {
  consolePanel.classList.toggle('input-top', inputOnTop);
  posBtn.textContent = inputOnTop ? '⇵' : '⇅';
  const label = inputOnTop ? 'Move the input below the output' : 'Move the input above the output';
  posBtn.title = label;
  posBtn.setAttribute('aria-label', label);
}
posBtn.addEventListener('click', () => {
  inputOnTop = !inputOnTop;
  try { localStorage.setItem('mobi-py-input-top', inputOnTop ? '1' : '0'); } catch { /* ignore */ }
  applyInputPos();
  if (runId) inputLine.focus();
});
applyInputPos();

/* --------------------- desktop terminal (xterm.js) ------------------- */
// On a wide screen the Terminal and REPL run under a real pseudoterminal and
// are drawn by xterm.js: you type straight at the prompt, with working Ctrl+C,
// arrow-key history and tab completion, and no Send button. If anything about
// that fails we quietly fall back to the line-based console below.
const termMount = $('#termMount');
let term = null;
let termFit = null;
let termWs = null;
let termRunId = null;
let xtermMods = null;
// Whether the program in the terminal has asked for bracketed paste. bash does,
// and pasted text should then arrive wrapped in the markers it expects.
let bracketedPaste = false;
const termDecoder = new TextDecoder();

function sendTermInput(text) {
  if (termWs && termWs.readyState === WebSocket.OPEN) {
    termWs.send(JSON.stringify({ type: 'input', text }));
  }
}

function noteTermModes(text) {
  if (text.includes('\x1b[?2004h')) bracketedPaste = true;
  if (text.includes('\x1b[?2004l')) bracketedPaste = false;
}

function isDesktop() {
  return window.matchMedia('(min-width: 860px)').matches;
}

function showTerminal(on) {
  consolePanel.classList.toggle('terminal-mode', on);
  termMount.hidden = !on;
}

async function loadXterm() {
  if (xtermMods) return xtermMods;
  const [core, addonFit] = await Promise.all([
    import('https://esm.sh/@xterm/xterm@5.5.0'),
    import('https://esm.sh/@xterm/addon-fit@0.10.0'),
  ]);
  xtermMods = { Terminal: core.Terminal, FitAddon: addonFit.FitAddon };
  return xtermMods;
}

function teardownTerminal() {
  if (termWs) { try { termWs.close(); } catch { /* ignore */ } termWs = null; }
  termRunId = null;
  showTerminal(false);
}

function onTermResize() {
  if (!termFit || termMount.hidden) return;
  try { termFit.fit(); } catch { /* ignore */ }
}

async function startPtyTerminal(nextMode) {
  try {
    const { Terminal, FitAddon } = await loadXterm();
    if (!term) {
      term = new Terminal({
        fontSize: 13,
        fontFamily: 'ui-monospace, SFMono-Regular, Menlo, Consolas, monospace',
        cursorBlink: true,
        scrollback: 2000,
        theme: {
          background: '#000000',
          foreground: '#e6edf3',
          cursor: '#58a6ff',
          selectionBackground: '#264f78',
        },
      });
      termFit = new FitAddon();
      term.loadAddon(termFit);
      term.open(termMount);
      // One handler for the life of the terminal; it follows the current socket.
      term.onData(sendTermInput);

      term.attachCustomKeyEventHandler((e) => {
        if (isCtrlActive && e.type === 'keydown') {
          if (['Control', 'Shift', 'Alt', 'Meta'].includes(e.key)) return false;
          if (e.key === 'Escape') {
            setCtrlActive(false);
            return false;
          }
          const ctrlChar = charToControlCode(e.key);
          setCtrlActive(false);
          if (ctrlChar) {
            sendControlCode(ctrlChar);
            return false;
          }
        }
        return true;
      });

      // Paste. Ctrl+V only pastes when the terminal's hidden textarea holds
      // focus, which is easy to lose — so take the paste event over ourselves in
      // the capture phase. That makes it work wherever the click landed, and
      // stops xterm from handling the same paste a second time.
      termMount.addEventListener('paste', (e) => {
        const text = e.clipboardData ? e.clipboardData.getData('text') : '';
        if (!text) return;
        e.preventDefault();
        e.stopPropagation();
        sendTermInput(bracketedPaste ? `\x1b[200~${text}\x1b[201~` : text);
      }, true);
      // Clicking the padding around the terminal should focus it too.
      termMount.addEventListener('mousedown', (e) => {
        if (e.target === termMount) { try { term.focus(); } catch { /* ignore */ } }
      });
      // Ctrl+V / Cmd+V pressed before the terminal has focus: give it focus, so
      // the paste lands here rather than nowhere.
      termMount.addEventListener('keydown', (e) => {
        if ((e.ctrlKey || e.metaKey) && (e.key === 'v' || e.key === 'V')) {
          try { term.focus(); } catch { /* ignore */ }
        }
      }, true);

      window.addEventListener('resize', onTermResize);
    }

    showTerminal(true);
    try { termFit.fit(); } catch { /* ignore */ }
    requestAnimationFrame(() => {
      try { termFit.fit(); } catch { /* ignore */ }
    });
    bracketedPaste = false;
    term.reset();
    term.focus();

    const res = await fetch('/api/runs', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ mode: nextMode, pty: true, cols: term.cols, rows: term.rows }),
    });
    const data = await res.json();
    if (!res.ok || !data.runId || !data.pty) throw new Error(data.error || 'no pty session');

    termRunId = data.runId;
    runId = data.runId;
    mode = data.mode;
    setRunning(true);
    setStatus('running', 'Running');

    const proto = location.protocol === 'https:' ? 'wss' : 'ws';
    termWs = new WebSocket(`${proto}://${location.host}/api/runs/${data.runId}/ws`);
    termWs.binaryType = 'arraybuffer';
    await new Promise((resolve, reject) => {
      const timer = setTimeout(() => reject(new Error('socket timed out')), 8000);
      termWs.onopen = () => { clearTimeout(timer); resolve(); };
      termWs.onerror = () => { clearTimeout(timer); reject(new Error('socket failed')); };
    });
    termWs.onmessage = (ev) => {
      if (ev.data instanceof ArrayBuffer) {
        const bytes = new Uint8Array(ev.data);
        noteTermModes(termDecoder.decode(bytes));
        term.write(bytes);
        return;
      }
      try {
        const msg = JSON.parse(ev.data);
        if (msg.type === 'text') { noteTermModes(msg.text); term.write(msg.text); }
        else if (msg.type === 'exit') onTerminalExit(msg);
      } catch { /* ignore */ }
    };
    termWs.onclose = () => {
      if (termRunId) { termRunId = null; runId = null; setRunning(false); }
    };
    return true;
  } catch {
    const orphan = runId;
    teardownTerminal();
    if (orphan) {
      try { await fetch(`/api/runs/${orphan}/kill`, { method: 'POST' }); } catch { /* ignore */ }
      runId = null;
    }
    return false;
  }
}

function onTerminalExit(msg) {
  const t = msg.elapsed_ms ? ` · ${(msg.elapsed_ms / 1000).toFixed(2)}s` : '';
  term.write(`\r\n\x1b[2m— session ended — press ▶ Run again\x1b[0m\r\n`);
  termRunId = null;
  runId = null;
  setRunning(false);
  setCtrlActive(false);
  if (msg.status === 'success') setStatus('success', `✓ Done${t}`);
  else if (msg.status === 'idle_timeout') setStatus('timeout', `⏱ Stopped: no activity${t}`);
  else if (msg.status === 'killed') setStatus('error', `■ Stopped${t}`);
  else setStatus('error', `✗ Error${t} · exit ${msg.exit_code ?? '?'}`);
}

/* --------------------------- capabilities ---------------------------- */
(async () => {
  try {
    const res = await fetch('/api/health');
    const h = await res.json();
    if (h.terminal) {
      const t = modebar.querySelector('[data-mode="terminal"]');
      if (t) t.hidden = false;
    }
    if (h.packages) pkgBtn.hidden = false;
    if (h.files) filesBtn.hidden = false;
    if (h.space_ttl_hours) spaceTtlHours = h.space_ttl_hours;
  } catch { /* offline: keep the defaults */ }
})();

window.mobiPy = {
  startRun,
  stopRun,
  getCode,
  setCode,
  setMode,
  setCtrlActive,
  charToControlCode,
  sendControlCode,
};
