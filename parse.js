// parse.js — a fast drop-in for marked 18.1.3 (default options: GFM on, breaks
// off, pedantic off, async off). parse(markdown) returns exactly the HTML that
// marked 18.1.3's marked.parse(markdown) returns, code unit for code unit.
//
// This file is a from-scratch reimplementation of marked's GFM parsing
// algorithm, written for speed. It is a fork of marked 18.1.3 (MIT, see
// NOTICE.md): the block and inline grammars, the tokenizers, the renderer and
// the helpers follow marked's algorithm, but the code is restructured around
// two ideas that make it measurably faster:
//
//  1. Position-based lexing. marked repeatedly slices the remaining source
//     (src.substring) and runs anchored regexes on the slices. Here the
//     lexers keep one index into the original string and run sticky (y)
//     regexes at that index, so no intermediate strings are ever built for
//     the scan itself.
//  2. First-character dispatch. Before trying a tokenizer, the loop looks at
//     the character at the current position and only tries the tokenizers
//     that can possibly match there (in marked's own order), skipping the
//     rest. Most positions can only ever be plain text.
//
// No network, no cache across parse() calls, no input recognition: every
// call computes its output from the markdown it is given. Dependency-free.

/* ------------------------------------------------------------------ */
/* Small regex-building helpers                                        */
/* ------------------------------------------------------------------ */

// edit() lets a pattern be assembled from named pieces, the way marked
// builds its grammars: replace(name, value) swaps the first occurrence of
// `name` in the pattern source for value's source (with ^-anchors inside a
// replacement kept, via the caret fix), getRegex() compiles the result.
function edit(pattern, flags = '') {
  let source = typeof pattern === 'string' ? pattern : pattern.source;
  const api = {
    replace(name, value) {
      let valueSource = typeof value === 'string' ? value : value.source;
      valueSource = valueSource.replace(/(^|[^\[])\^/g, '$1');
      source = source.replace(name, valueSource);
      return api;
    },
    getRegex() {
      return new RegExp(source, flags);
    },
  };
  return api;
}

// A sticky clone of an anchored pattern: the leading ^ is dropped (the
// sticky flag anchors the match at lastIndex instead) and the global flag
// is swapped for sticky. Used for every regex the lexers run at a position.
function stickyOf(regex) {
  const src = regex.source;
  const clean = src.charCodeAt(0) === 94 ? src.slice(1) : src; // 94 === '^'
  const flags = (regex.flags.replace('g', '') + 'y');
  return new RegExp(clean, flags);
}

const supportsLookbehind = (() => {
  try {
    return !!new RegExp('(?<=1)(?<!1)');
  } catch {
    return false;
  }
})();

/* ------------------------------------------------------------------ */
/* Shared ("other") patterns — used by .test/.match/.replace on short   */
/* strings, so they stay ordinary (non-sticky) regexes.                */
/* ------------------------------------------------------------------ */

const TAG_NAMES =
  'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';

const O = {
  codeRemoveIndent: /^(?: {0,3}\t| {1,4})/gm,
  outputLinkReplace: /\\([\[\]])/g,
  indentCodeCompensation: /^(\s+)(?:```)/,
  beginningSpace: /^\s+/,
  endingHash: /#$/,
  startingSpaceChar: /^ /,
  endingSpaceChar: / $/,
  endingSpaceTabChar: /[ \t]$/,
  nonSpaceChar: /[^ ]/,
  newLineCharGlobal: /\n/g,
  tabCharGlobal: /\t/g,
  leadingSpaceTab: /^[ \t]+/,
  multipleSpaceGlobal: /\s+/g,
  blankLine: /^[ \t]*$/,
  doubleBlankLine: /\n[ \t]*\n[ \t]*$/,
  blockquoteStart: /^ {0,3}>/,
  blockquoteSetextReplace: /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g,
  blockquoteSetextReplace2: /^ {0,3}>[ \t]?/gm,
  blockquoteMarkerWhitespace: /^( {0,3}>)([ \t]+)/gm,
  listReplaceNesting: /^ {1,4}(?=( {4})*[^ ])/g,
  listIsTask: /^\[[ xX]\][ \t]+\S/,
  listReplaceTask: /^\[[ xX]\][ \t]+/,
  listTaskCheckbox: /\[[ xX]\]/,
  anyLine: /\n.*\n/,
  hrefBrackets: /^<(.*)>$/,
  tableDelimiter: /[:|]/,
  tableAlignChars: /^\||\| *$/g,
  tableRowBlankLine: /\n[ \t]*$/,
  tableAlignRight: /^ *-+: *$/,
  tableAlignCenter: /^ *:-+: *$/,
  tableAlignLeft: /^ *:-+ *$/,
  startATag: /^<a /i,
  endATag: /^<\/a>/i,
  startPreScriptTag: /^<(pre|code|kbd|script)(\s|>)/i,
  endPreScriptTag: /^<\/(pre|code|kbd|script)(\s|>)/i,
  startAngleBracket: /^</,
  endAngleBracket: />$/,
  unicodeAlphaNumeric: /[\p{L}\p{N}]/u,
  numericCharacterReference: /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/,
  numericCharacterReferenceOrAmpersand: /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g,
  escapeTest: /[&<>"']/,
  escapeReplace: /[&<>"']/g,
  escapeTestNoEncode: /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/,
  escapeReplaceNoEncode: /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g,
  caret: /(^|[^\[])\^/g,
  percentDecode: /%25/g,
  findPipe: /\|/g,
  splitPipe: / \|/,
  slashPipe: /\\\|/g,
  carriageReturn: /\r\n|\r/g,
  spaceLine: /^ +$/gm,
  notSpaceStart: /^\S*/,
  endingNewline: /\n$/,
};

// Per-indent regexes for the list tokenizer, cached by indent (0..3).
function cachedIndentRegex(build) {
  const cache = [];
  return (indent) => {
    const idx = Math.max(0, Math.min(3, indent - 1));
    let re = cache[idx];
    if (!re) {
      re = build(idx);
      cache[idx] = re;
    }
    return re;
  };
}

O.listItemRegex = (bull) => stickyOf(new RegExp(`^( {0,3}${bull})((?:[\t ][^\n]*)?(?:\n|$))`));
O.nextBulletRegex = cachedIndentRegex((i) => stickyOf(new RegExp(`^ {0,${i}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\n]*)?(?:\n|$))`)));
O.hrRegex = cachedIndentRegex((i) => stickyOf(new RegExp(`^ {0,${i}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\n+|$)`)));
O.fencesBeginRegex = cachedIndentRegex((i) => stickyOf(new RegExp(`^ {0,${i}}(?:\`\`\`|~~~)`)));
O.headingBeginRegex = cachedIndentRegex((i) => stickyOf(new RegExp(`^ {0,${i}}#{1,6}(?:\\s|$)`)));
O.htmlBeginRegex = cachedIndentRegex((i) => stickyOf(new RegExp(`^ {0,${i}}(?:</?(?:${TAG_NAMES})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i')));
O.blockquoteBeginRegex = cachedIndentRegex((i) => stickyOf(new RegExp(`^ {0,${i}}>`)));

/* ------------------------------------------------------------------ */
/* Block grammar (GFM). Every pattern is anchored at the start; the     */
/* lexers run the sticky clone of each at the current position.          */
/* ------------------------------------------------------------------ */

const BLOCK = {};
{
  const bullet = / {0,3}(?:[*+-]|\d{1,9}[.)])/;
  const hrSrc = ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';
  const headingSrc = ' {0,3}#{1,6}(?:\\s|$)';
  const fencesSrc = ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)';
  const blockquoteSrc = ' {0,3}>';
  const htmlStartSrc = ' {0,3}(?:</?(?:' + TAG_NAMES + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)';

  BLOCK.newline = stickyOf(/^(?:[ \t]*(?:\n|$))+/);
  BLOCK.code = stickyOf(/^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/);
  BLOCK.fences = stickyOf(/^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/);
  BLOCK.hr = stickyOf(/^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/);
  BLOCK.heading = stickyOf(/^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/);

  const lheadingCore = /^(?!bull |blockCode|fences|blockquote|heading|html|table)((?:.|\n(?!\s*?\n|bull |fences|blockquote|heading|hr|html|table))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/;
  BLOCK.lheading = stickyOf(edit(lheadingCore)
    .replace(/bull/g, bullet)
    .replace(/blockCode/g, /(?: {4}| {0,3}\t)/)
    .replace(/fences/g, / {0,3}(?:`{3,}|~{3,})/)
    .replace(/blockquote/g, / {0,3}>/)
    .replace(/heading/g, / {0,3}#{1,6}(?:\s|$)/)
    .replace(/hr/g, / {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/)
    .replace(/html/g, / {0,3}<[^\n>]+>\n/)
    .replace(/table/g, / {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n/)
    .getRegex());

  const paragraphCore = /^([^\n]+(?:\n(?!hr|heading|lheading|blockquote|fences|list|html|table|[ \t]+\n)[^\n]+)*)/;
  BLOCK.paragraph = stickyOf(edit(paragraphCore)
    .replace('hr', new RegExp(hrSrc))
    .replace('heading', headingSrc)
    .replace('|lheading', '')
    .replace('table', edit(
      '^ *([^\\n ].*)\\n'
      + ' {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)'
      + '(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)')
      .replace('hr', new RegExp(hrSrc))
      .replace('heading', headingSrc)
      .replace('blockquote', blockquoteSrc)
      .replace('code', /(?: {4}| {0,3}\t)[^\n]/)
      .replace('fences', new RegExp(fencesSrc))
      .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]')
      .replace('html', htmlStartSrc)
      .replace('tag', TAG_NAMES)
      .getRegex())
    .replace('blockquote', blockquoteSrc)
    .replace('fences', new RegExp(fencesSrc))
    .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]')
    .replace('html', htmlStartSrc)
    .replace('tag', TAG_NAMES)
    .getRegex());

  BLOCK.text = stickyOf(/^[^\n]+/);

  const blockLabel = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+/;
  BLOCK.def = stickyOf(edit(/^ {0,3}\[(label)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)(title))? *(?:\n+|$)/)
    .replace('label', blockLabel)
    .replace('title', /(?:\"(?:\\[\s\S]|[^\"\\])*\"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))/)
    .getRegex());

  BLOCK.list = stickyOf(edit(/^(bull)([ \t][^\n]*?)?(?:\n|$)/)
    .replace(/bull/g, bullet)
    .getRegex());

  const comment = /<!--(?:-?>|[\s\S]*?(?:-->|$))/;
  BLOCK.html = stickyOf(edit(
    '^ {0,3}(?:'
    + '<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)'
    + '|comment[^\\n]*(\\n+|$)'
    + '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)'
    + '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)'
    + '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)'
    + '|</?(tag)(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)'
    + '|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:attribute)*? */?>(?=[ \t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)'
    + '|</[a-z][a-z0-9-]*\\s*>(?=[ \t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$))', 'i')
    .replace('comment', comment)
    .replace('tag', TAG_NAMES)
    .replace('attribute', / +[a-zA-Z:_][\w.:-]*(?: *= *\"[^\"\n]*\"| *= *'[^'\n]*'| *= *[^\s\"'=<>`]+)?/)
    .getRegex());

  BLOCK.table = stickyOf(edit(
    '^ *([^\\n ].*)\\n'
    + ' {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)'
    + '(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)')
    .replace('hr', new RegExp(hrSrc))
    .replace('heading', headingSrc)
    .replace('blockquote', blockquoteSrc)
    .replace('code', /(?: {4}| {0,3}\t)[^\n]/)
    .replace('fences', new RegExp(fencesSrc))
    .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]')
    .replace('html', htmlStartSrc)
    .replace('tag', TAG_NAMES)
    .getRegex());

  const blockquoteParagraph = edit(paragraphCore)
    .replace('hr', new RegExp(hrSrc))
    .replace('heading', headingSrc)
    .replace('|lheading', '')
    .replace('|table', '')
    .replace('blockquote', blockquoteSrc)
    .replace('fences', new RegExp(fencesSrc))
    .replace('list', / {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)/)
    .replace('html', htmlStartSrc)
    .replace('tag', TAG_NAMES)
    .getRegex();
  BLOCK.blockquote = stickyOf(edit(/^( {0,3}> ?(?:(?![ \t]*(?:\n|$))(paragraph)|[^\n]*)(?:\n|$))+/)
    .replace('paragraph', blockquoteParagraph)
    .getRegex());
}

/* ------------------------------------------------------------------ */
/* Inline grammar (GFM). Sticky clones for the patterns the inline     */
/* lexer runs at a position; the global ones are only used for          */
/* replace/matchAll, so they stay as marked built them.                 */
/* ------------------------------------------------------------------ */

const INLINE = {};
{
  const punct = /[\p{P}\p{S}]/u;
  const punctOrSpace = /[\s\p{P}\p{S}]/u;
  const notPunctOrSpace = /[^\s\p{P}\p{S}]/u;
  const punctGfm = /(?!~)[\p{P}\p{S}]/u;
  const punctOrSpaceGfm = /(?!~)[\s\p{P}\p{S}]/u;
  const notPunctOrSpaceGfm = /(?:[^\s\p{P}\p{S}]|~)/u;

  INLINE.escape = new RegExp("\\\\([!\"#$%&'()*+,\\-./:;<=>?@\\[\\]\\\\^_`{|}~])", 'y');
  INLINE.code = new RegExp("(`+)([^`]|[^`][\\s\\S]*?[^`])\\1(?!`)", 'y');
  INLINE.br = new RegExp("( {2,}|\\\\)\\n(?!\\s*$)[ \\t]*", 'y');
  INLINE.punctuation = edit(/^((?![*_])punctSpace)/, 'u')
    .replace(/punctSpace/g, punctOrSpace).getRegex();

  INLINE.blockSkip = new RegExp("\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)|(?<!`)()(?<b>`+)[^`]+\\k<b>(?!`)|<(?! )[^<>]*?>", 'g');

  const emStrongLDelimCore = /^(?:\*+(?:((?!\*)punct)|([^\s*]))?|_+(?:((?!_)punct)|([^\s_]))?)/;
  INLINE.emStrongLDelim = stickyOf(edit(emStrongLDelimCore, 'u')
    .replace(/punct/g, punctGfm).getRegex());

  const emStrongRDelimAstCore =
    '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)'
    + '|[^*]+(?=[^*])'
    + '|(?!\\*)punct(\\*+)(?=[\\s]|$)'
    + '|notPunctSpace(\\*+)(?!\\*)(?=punctSpace|$)'
    + '|(?!\\*)punctSpace(\\*+)(?=notPunctSpace)'
    + '|[\\s](\\*+)(?!\\*)(?=punct)'
    + '|(?!\\*)punct(\\*+)(?!\\*)(?=punct)'
    + '|notPunctSpace(\\*+)(?=notPunctSpace)';
  INLINE.emStrongRDelimAst = edit(emStrongRDelimAstCore, 'gu')
    .replace(/notPunctSpace/g, notPunctOrSpaceGfm)
    .replace(/punctSpace/g, punctOrSpaceGfm)
    .replace(/punct/g, punctGfm).getRegex();

  INLINE.emStrongRDelimUnd = edit(
    '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)'
    + '|[^_]+(?=[^_])'
    + '|(?!_)punct(_+)(?=[\\s]|$)'
    + '|notPunctSpace(_+)(?!_)(?=punctSpace|$)'
    + '|(?!_)punctSpace(_+)(?=notPunctSpace)'
    + '|[\\s](_+)(?!_)(?=punct)'
    + '|(?!_)punct(_+)(?!_)(?=punct)', 'gu')
    .replace(/notPunctSpace/g, notPunctOrSpace)
    .replace(/punctSpace/g, punctOrSpace)
    .replace(/punct/g, punct).getRegex();

  INLINE.delLDelim = stickyOf(edit(/^~~?(?:((?!~)punct)|[^\s~])/, 'u')
    .replace(/punct/g, punct).getRegex());

  INLINE.delRDelim = edit(
    '^[^~]+(?=[^~])'
    + '|(?!~)punct(~~?)(?=[\\s]|$)'
    + '|notPunctSpace(~~?)(?!~)(?=punctSpace|$)'
    + '|(?!~)punctSpace(~~?)(?=notPunctSpace)'
    + '|[\\s](~~?)(?!~)(?=punct)'
    + '|(?!~)punct(~~?)(?!~)(?=punct)'
    + '|notPunctSpace(~~?)(?=notPunctSpace)', 'gu')
    .replace(/notPunctSpace/g, notPunctOrSpace)
    .replace(/punctSpace/g, punctOrSpace)
    .replace(/punct/g, punct).getRegex();

  INLINE.anyPunctuation = new RegExp("\\\\([\\p{P}\\p{S}])", 'gu');
  INLINE.anyPunctuationOutsideCode = new RegExp("(`+)(?:[^`]|[^`][\\s\\S]*?[^`])\\1(?!`)|`+|\\\\([\\p{P}\\p{S}])", 'gu');

  INLINE.tag = new RegExp("<!--(?:-?>|[\\s\\S]*?-->)|<\\/[a-zA-Z][a-zA-Z0-9-]*\\s*>|<[a-zA-Z][a-zA-Z0-9-]*(?:\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*\"[^\"]*\"|\\s*=\\s*'[^']*'|\\s*=\\s*[^\\s\"'=<>`]+)?)*?\\s*\\/?>|<\\?[\\s\\S]*?\\?>|<![a-zA-Z]+\\s[\\s\\S]*?>|<!\\[CDATA\\[[\\s\\S]*?\\]\\]>", 'y');
  INLINE.link = new RegExp("!?\\[((?:\\[(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?)\\]\\([ \\t\\n]*(<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\)))(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(\"(?:\\\\[\\s\\S]|[^\"\\\\])*\"|'(?:\\\\[\\s\\S]|[^'\\\\])*'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)))?[ \\t\\n]*\\)", 'y');
  INLINE.reflink = new RegExp("!?\\[((?:\\[(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?)\\]\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+)\\]", 'y');
  INLINE.nolink = new RegExp("!?\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+)\\](?:\\[\\])?", 'y');
  INLINE.reflinkSearch = new RegExp("!?\\[((?:[^\\[\\]\\\\`]*(?:\\[(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?)\\]\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999})\\]|!?\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999})\\](?:\\[\\])?(?!\\()", 'g');
  INLINE.autolink = new RegExp("<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\\s\\x00-\\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>", 'y');
  INLINE.url = new RegExp("(?:mailto:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])|xmpp:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])(?:\\/[A-Za-z0-9@.]+)?)|((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*|[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])", 'y');
  INLINE._backpedal = /(?:[^?!.,:;*_'\"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'\"~)]+(?!$))+/;
  INLINE.text = new RegExp("(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\\n)|(?=[a-zA-Z0-9.!#$%&'*+\\/=?_`{\\|}~-]+@)|[\\s\\S]*?(?:(?=[\\\\<!\\[`*~_]|\\b_|[hH][tT][tT][pP][sS]?|[fF][tT][pP]:\\/\\/|(?<![^\\s*_~(])www\\.|$)|[^ ](?= {2,}\\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)|[^a-zA-Z0-9.!#$%&'*+\\/=?_`{\\|}~-](?=[a-zA-Z0-9.!#$%&'*+\\/=?_`{\\|}~-]+@))))", 'y');
}

/* ------------------------------------------------------------------ */
/* Helpers                                                             */
/* ------------------------------------------------------------------ */

const ESCAPE_REPLACEMENTS = {
  '&': '&amp;',
  '<': '&lt;',
  '>': '&gt;',
  '"': '&quot;',
  "'": '&#39;',
};

function escapeHtmlEntities(html, encode) {
  if (encode) {
    if (O.escapeTest.test(html)) {
      return html.replace(O.escapeReplace, (ch) => ESCAPE_REPLACEMENTS[ch]);
    }
  } else if (O.escapeTestNoEncode.test(html)) {
    return html.replace(O.escapeReplaceNoEncode, (ch) => ESCAPE_REPLACEMENTS[ch]);
  }
  return html;
}

function decodeNumericCharacterReferences(text) {
  if (!O.numericCharacterReference.test(text)) {
    return text;
  }
  return text.replace(O.numericCharacterReferenceOrAmpersand, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) {
      return '&amp;';
    }
    const code = dec === undefined ? Number.parseInt(hex, 16) : Number.parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) {
      return '�';
    }
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

function cleanUrl(href) {
  try {
    href = encodeURI(href).replace(O.percentDecode, '%');
  } catch {
    return null;
  }
  return href;
}

function splitCells(tableRow, count) {
  const row = tableRow.replace(O.findPipe, (match, offset, str) => {
    let escaped = false;
    let curr = offset;
    while (--curr >= 0 && str[curr] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = row.split(O.splitPipe);
  let i = 0;
  if (!cells[0].trim()) {
    cells.shift();
  }
  if (cells.length > 0 && !cells.at(-1)?.trim()) {
    cells.pop();
  }
  if (count) {
    if (cells.length > count) {
      cells.splice(count);
    } else {
      while (cells.length < count) cells.push('');
    }
  }
  for (; i < cells.length; i++) {
    cells[i] = cells[i].trim().replace(O.slashPipe, '|');
  }
  return cells;
}

// Remove trailing `c`s (or, with invert, trailing non-`c`s). A /c*$/ regex
// would be vulnerable to catastrophic backtracking, hence the loop.
function rtrim(str, c, invert) {
  const len = str.length;
  if (len === 0) {
    return '';
  }
  let suffixLen = 0;
  while (suffixLen < len) {
    const currChar = str.charAt(len - suffixLen - 1);
    if (currChar === c && !invert) {
      suffixLen++;
    } else if (currChar !== c && invert) {
      suffixLen++;
    } else {
      break;
    }
  }
  return str.slice(0, len - suffixLen);
}

function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && O.blankLine.test(lines[end])) {
    end--;
  }
  if (lines.length - end <= 2) {
    return str;
  }
  return lines.slice(0, end + 1).join('\n');
}

// A link label, folded the way CommonMark asks: trim, collapse inner
// whitespace runs to one space, Unicode case-fold via upper-then-lower.
function normalizeLabel(label) {
  return label.trim().replace(O.multipleSpaceGlobal, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Index of the closing bracket that takes `str` below zero depth, or -1
// when balanced and -2 when more opens than closes. A backslash skips the
// next character.
function findClosingBracket(str, brackets) {
  if (str.indexOf(brackets[0]) === -1 && str.indexOf(brackets[1]) === -1) {
    return -1;
  }
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    if (str[i] === '\\') {
      i++;
    } else if (str[i] === brackets[0]) {
      level++;
    } else if (str[i] === brackets[1]) {
      level--;
      if (level < 0) {
        return i;
      }
    }
  }
  if (level > 0) {
    return -2;
  }
  return -1;
}

function expandTabs(line, indent = 0) {
  let col = indent;
  let expanded = '';
  for (const char of line) {
    if (char === '\t') {
      const added = 4 - (col % 4);
      expanded += ' '.repeat(added);
      col += added;
    } else {
      expanded += char;
      col++;
    }
  }
  return expanded;
}

// One scan of a masked inline source for the last emphasis, strong and
// strikethrough closers, shared by every opener in the pass. The frames
// live on a stack per tokenizer so nested inline passes do not clash, and
// the entry is dropped when the outermost pass ends so the source is not
// retained.
const closerHintStacks = new WeakMap();

function scanClosers(src) {
  const lastEmStrong = { '*': -1, '_': -1 };
  let lastDel = -1;
  const len = src.length;
  for (let i = 0; i < len; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') {
      continue;
    }
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    while (j < len && src[j] === ch) {
      j++;
    }
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') {
        lastDel = i;
      } else {
        lastEmStrong[ch] = i;
      }
    }
    i = j - 1;
  }
  return { maskedSrc: src, lastEmStrong, lastDel };
}

function beginCloserScan(tokenizer, maskedSrc) {
  const frame = scanClosers(maskedSrc);
  const stack = closerHintStacks.get(tokenizer);
  if (stack) {
    stack.push(frame);
  } else {
    closerHintStacks.set(tokenizer, [frame]);
  }
}

function endCloserScan(tokenizer) {
  const stack = closerHintStacks.get(tokenizer);
  if (!stack) {
    return;
  }
  stack.pop();
  if (stack.length === 0) {
    closerHintStacks.delete(tokenizer);
  }
}

function cachedEmStrongCloserIndex(tokenizer, maskedSrc, delim) {
  const frame = closerHintStacks.get(tokenizer)?.at(-1);
  if (frame && frame.maskedSrc === maskedSrc) {
    return frame.lastEmStrong[delim];
  }
  return scanClosers(maskedSrc).lastEmStrong[delim];
}

function cachedDelCloserIndex(tokenizer, maskedSrc) {
  const frame = closerHintStacks.get(tokenizer)?.at(-1);
  if (frame && frame.maskedSrc === maskedSrc) {
    return frame.lastDel;
  }
  return scanClosers(maskedSrc).lastDel;
}

/* ------------------------------------------------------------------ */
/* Tokenizer helpers                                                   */
/* ------------------------------------------------------------------ */

// execAt runs a sticky regex at a position and returns its match (or
// null). Every tokenizer below works on (src, pos) this way instead of
// slicing the remaining source.
function execAt(re, src, pos) {
  re.lastIndex = pos;
  return re.exec(src);
}

function outputLink(cap, link, raw, lexer) {
  const href = link.href;
  const title = link.title || null;
  const text = cap[1].replace(O.outputLinkReplace, '$1');
  const isImage = cap[0].charAt(0) === '!';

  const outerInLink = lexer.state.inLink;
  const outerLinkEmitted = lexer.state.linkEmitted;
  const outerInRawBlock = lexer.state.inRawBlock;
  lexer.state.inLink = true;
  lexer.state.linkEmitted = false;
  const tokens = lexer.inlineTokens(text);
  const textHasLink = lexer.state.linkEmitted;
  lexer.state.linkEmitted = outerLinkEmitted;
  lexer.state.inLink = outerInLink;

  if (!isImage) {
    // CommonMark: "Links may not contain other links, at any level of
    // nesting." Bail so the caller falls through to text and the inner link
    // is the one kept. Images are exempt: their text is flattened into an
    // alt attribute.
    if (textHasLink) {
      lexer.state.inRawBlock = outerInRawBlock;
      return;
    }
    lexer.state.linkEmitted = true;
  }

  return {
    type: isImage ? 'image' : 'link',
    raw,
    href,
    title,
    text,
    tokens,
  };
}

function indentCodeCompensation(raw, text) {
  const matchIndentToCode = raw.match(O.indentCodeCompensation);
  if (matchIndentToCode === null) {
    return text;
  }
  const indentToCode = matchIndentToCode[1];
  return text
    .split('\n')
    .map((node) => {
      const matchIndentInNode = node.match(O.beginningSpace);
      if (matchIndentInNode === null) {
        return node;
      }
      const [indentInNode] = matchIndentInNode;
      return node.slice(Math.min(indentInNode.length, indentToCode.length));
    })
    .join('\n');
}

// Is the label's end inside a tag or autolink that runs past it? `src` is
// the whole source and `pos` the position the link starts at.
function isLabelEndInsideToken(src, pos, label, labelStart) {
  if (!label.includes('<')) {
    return false;
  }
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') {
      i++;
      continue;
    }
    if (label[i] === '`') {
      const code = execAt(INLINE.code, label, i);
      if (code) {
        i += code[0].length - 1;
        continue;
      }
    }
    if (label[i] !== '<') {
      continue;
    }
    const tokenSrc = src.slice(pos + labelStart + i);
    const token = execAt(INLINE.tag, tokenSrc, 0) || execAt(INLINE.autolink, tokenSrc, 0);
    if (!token) {
      continue;
    }
    if (token[0].length > label.length - i) {
      return true;
    }
    i += token[0].length - 1;
  }
  return false;
}

/* ------------------------------------------------------------------ */
/* Tokenizer — every method takes (src, pos) and returns a token, or    */
/* undefined when it does not match at that position. The token's raw   */
/* is the matched text, so the caller advances pos by raw.length.       */
/* ------------------------------------------------------------------ */

class Tokenizer {
  constructor() {
    this.lexer = null;
  }

  space(src, pos) {
    const cap = execAt(BLOCK.newline, src, pos);
    if (cap && cap[0].length > 0) {
      return { type: 'space', raw: cap[0] };
    }
  }

  code(src, pos) {
    const cap = execAt(BLOCK.code, src, pos);
    if (cap) {
      const raw = trimTrailingBlankLines(cap[0]);
      const text = raw.replace(O.codeRemoveIndent, '');
      return { type: 'code', raw, codeBlockStyle: 'indented', text };
    }
  }

  fences(src, pos) {
    const cap = execAt(BLOCK.fences, src, pos);
    if (cap) {
      const raw = cap[0];
      const text = indentCodeCompensation(raw, cap[3] || '');
      return {
        type: 'code',
        raw,
        lang: cap[2] ? cap[2].trim().replace(INLINE.anyPunctuation, '$1') : cap[2],
        text,
      };
    }
  }

  heading(src, pos) {
    const cap = execAt(BLOCK.heading, src, pos);
    if (cap) {
      let text = cap[2].trim();
      // Remove trailing #s.
      if (O.endingHash.test(text)) {
        const trimmed = rtrim(text, '#');
        if (!trimmed || O.endingSpaceTabChar.test(trimmed)) {
          // CommonMark requires a space or tab before trailing #s.
          text = trimmed.trim();
        }
      }
      return {
        type: 'heading',
        raw: rtrim(cap[0], '\n'),
        depth: cap[1].length,
        text,
        tokens: this.lexer.inline(text),
      };
    }
  }

  hr(src, pos) {
    const cap = execAt(BLOCK.hr, src, pos);
    if (cap) {
      return { type: 'hr', raw: rtrim(cap[0], '\n') };
    }
  }

  blockquote(src, pos) {
    const cap = execAt(BLOCK.blockquote, src, pos);
    if (cap) {
      let lines = rtrim(cap[0], '\n').split('\n');
      let raw = '';
      let text = '';
      const tokens = [];

      while (lines.length > 0) {
        let inBlockquote = false;
        const currentLines = [];
        let i;
        for (i = 0; i < lines.length; i++) {
          if (O.blockquoteStart.test(lines[i])) {
            currentLines.push(lines[i]);
            inBlockquote = true;
          } else if (!inBlockquote) {
            currentLines.push(lines[i]);
          } else {
            break;
          }
        }
        lines = lines.slice(i);

        const currentRaw = currentLines.join('\n');
        const currentText = currentRaw
          // A tab after the block quote marker runs to the next tab stop,
          // and the marker only consumes one space of it; the rest is content.
          .replace(
            O.blockquoteMarkerWhitespace,
            (_, marker, whitespace) => marker + expandTabs(whitespace, marker.length),
          )
          // Precede setext continuation with 4 spaces so it isn't a setext.
          .replace(O.blockquoteSetextReplace, '\n    $1')
          .replace(O.blockquoteSetextReplace2, '');
        raw = raw ? `${raw}\n${currentRaw}` : currentRaw;
        text = text ? `${text}\n${currentText}` : currentText;

        // Parse blockquote lines as top level tokens; merge paragraphs if
        // this is a continuation.
        const top = this.lexer.state.top;
        this.lexer.state.top = true;
        this.lexer.blockTokens(currentText, tokens, true);
        this.lexer.state.top = top;

        if (lines.length === 0) {
          break;
        }

        const lastToken = tokens.at(-1);
        if (lastToken?.type === 'code' || lastToken?.type === 'heading' || lastToken?.type === 'hr' || lastToken?.type === 'html' || lastToken?.type === 'table') {
          // Blockquote continuation cannot be preceded by a code block,
          // heading, hr, html block or table.
          break;
        } else if (lastToken?.type === 'blockquote') {
          const oldToken = lastToken;
          // The continuation lines belong to the same nesting frame as the
          // nested blockquote, which already had one '>' marker stripped, so
          // strip one marker from them too.
          const continuation = lines.join('\n');
          const newText = oldToken.raw + '\n' + continuation.replace(O.blockquoteSetextReplace2, '');
          const newToken = this.blockquote(newText, 0);
          tokens[tokens.length - 1] = newToken;
          // Only include continuation lines the nested blockquote actually
          // consumed. Unconsumed trailing lines must stay out of `raw`.
          const leftover = newText.substring(newToken.raw.length).replace(/^\n/, '');
          const leftoverCount = leftover ? leftover.split('\n').length : 0;
          const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
          if (consumed.length > 0) {
            raw = `${raw}\n${consumed.join('\n')}`;
          }
          text = text.substring(0, text.length - oldToken.text.length) + newToken.text;
          // A leftover line that starts with '>' still belongs to this
          // blockquote; any other leftover line ends it.
          lines = lines.slice(consumed.length);
          if (lines.length > 0 && O.blockquoteStart.test(lines[0])) {
            continue;
          }
          break;
        } else if (lastToken?.type === 'list') {
          const oldToken = lastToken;
          const newText = oldToken.raw + '\n' + lines.join('\n');
          const newToken = this.list(newText, 0);
          tokens[tokens.length - 1] = newToken;
          // The list raw has no '>' markers, so it cannot be cut out of
          // `raw`. Count the continuation lines the list took instead.
          const consumedCount = newToken.raw.length > oldToken.raw.length
            ? newText.slice(oldToken.raw.length + 1, newToken.raw.length).split('\n').length
            : 0;
          if (consumedCount > 0) {
            const consumed = lines.slice(0, consumedCount).join('\n');
            raw = `${raw}\n${consumed}`;
            text = `${text}\n${consumed}`;
          }
          lines = lines.slice(consumedCount);
          continue;
        }
      }

      return { type: 'blockquote', raw, tokens, text };
    }
  }

  list(src, startPos) {
    let p = startPos;
    let cap = execAt(BLOCK.list, src, p);
    if (!cap) {
      return;
    }
    // The source is only consumed from the front, so every raw below is a
    // slice of it between absolute positions.
    const listStart = startPos;
    let bull = cap[1].trim();
    const isordered = bull.length > 1;

    const list = {
      type: 'list',
      raw: '',
      ordered: isordered,
      start: isordered ? +bull.slice(0, -1) : '',
      loose: false,
      items: [],
    };

    bull = isordered ? `\\d{1,9}\\${bull.slice(-1)}` : `\\${bull}`;

    // Get next list item.
    const itemRegex = O.listItemRegex(bull);
    let endsWithBlankLine = false;
    while (p < src.length) {
      let endEarly = false;
      let itemContents = '';
      if (!(cap = execAt(itemRegex, src, p))) {
        break;
      }
      // End list if bullet was actually an HR.
      if (execAt(BLOCK.hr, src, p)) {
        break;
      }

      const itemStart = p;
      p += cap[0].length;

      const firstLineRaw = cap[2];
      const firstNl = firstLineRaw.indexOf('\n');
      const firstLine = firstNl === -1 ? firstLineRaw : firstLineRaw.slice(0, firstNl);
      const bulletIndent = cap[1].length;
      let line = firstLine.replace(O.leadingSpaceTab, (whitespace) => expandTabs(whitespace, bulletIndent));
      let nextLineEnd = src.indexOf('\n', p);
      let nextLine = nextLineEnd === -1 ? src.slice(p) : src.slice(p, nextLineEnd);
      let blankLine = !line.trim();

      let indent = 0;
      if (blankLine) {
        indent = bulletIndent + 1;
      } else {
        indent = line.search(O.nonSpaceChar);
        // Treat indented code blocks (> 4 spaces) as having only 1 indent.
        indent = indent > 4 ? 1 : indent;
        itemContents = line.slice(indent);
        indent += bulletIndent;
      }

      if (blankLine && O.blankLine.test(nextLine)) {
        // Items begin with at most one blank line.
        p = nextLineEnd === -1 ? src.length : nextLineEnd + 1;
        endEarly = true;
      }

      if (!endEarly) {
        const nextBulletRegex = O.nextBulletRegex(indent);
        const hrRegex = O.hrRegex(indent);
        const fencesBeginRegex = O.fencesBeginRegex(indent);
        const headingBeginRegex = O.headingBeginRegex(indent);
        const htmlBeginRegex = O.htmlBeginRegex(indent);
        const blockquoteBeginRegex = O.blockquoteBeginRegex(indent);

        // Check if following lines should be included in the list item.
        while (p < src.length) {
          const lineEnd = src.indexOf('\n', p);
          const rawLine = lineEnd === -1 ? src.slice(p) : src.slice(p, lineEnd);
          let nextLine = rawLine;
          // ExpandTabs only matters when a tab is present; skip the
          // replace (and its allocation) for the common tab-free line.
          let nextLineWithoutTabs = nextLine.includes('\t')
            ? nextLine.replace(O.leadingSpaceTab, (whitespace) => expandTabs(whitespace))
            : nextLine;

          // First-character dispatch for the six block-start checks: each
          // pattern is `^ {0,indent}<char>...`, so it can only match when
          // the first non-space character sits within `indent` spaces and
          // is that pattern's opener. A plain-text line runs none of them.
          let fi = 0;
          while (fi < nextLine.length && nextLine[fi] === ' ') fi++;
          const firstCh = fi < nextLine.length ? nextLine[fi] : '';
          if (firstCh !== '' && firstCh !== '\t' && fi <= indent) {
            if ((firstCh === '`' || firstCh === '~') && execAt(fencesBeginRegex, nextLine, 0)) {
              break; // End list item if found code fences.
            }
            if (firstCh === '#' && execAt(headingBeginRegex, nextLine, 0)) {
              break; // End list item if found start of new heading.
            }
            if (firstCh === '<' && execAt(htmlBeginRegex, nextLine, 0)) {
              break; // End list item if found start of html block.
            }
            if (firstCh === '>' && execAt(blockquoteBeginRegex, nextLine, 0)) {
              break; // End list item if found start of blockquote.
            }
            if ((firstCh === '*' || firstCh === '+' || firstCh === '-'
                || (firstCh >= '0' && firstCh <= '9'))
              && execAt(nextBulletRegex, nextLine, 0)) {
              break; // End list item if found start of new bullet.
            }
            if ((firstCh === '-' || firstCh === '_' || firstCh === '*')
              && execAt(hrRegex, nextLine, 0)) {
              break; // Horizontal rule found.
            }
          }

          // Dedent if possible.
          if (nextLineWithoutTabs.search(O.nonSpaceChar) >= indent || !nextLine.trim()) {
            itemContents += '\n' + nextLineWithoutTabs.slice(indent);
          } else {
            // Not enough indentation.
            if (blankLine) {
              break;
            }
            // Paragraph continuation unless last line was a different block
            // level element.
            if (line.replace(O.tabCharGlobal, '    ').search(O.nonSpaceChar) >= 4) {
              // Indented code block.
              break;
            }
            if (execAt(fencesBeginRegex, line, 0)) {
              break;
            }
            if (execAt(headingBeginRegex, line, 0)) {
              break;
            }
            if (execAt(htmlBeginRegex, line, 0)) {
              break;
            }
            if (execAt(hrRegex, line, 0)) {
              break;
            }
            // A lazy continuation can look like a setext underline after
            // list indentation is removed. Keep it in the paragraph.
            const setextContinuation = /^ {0,3}(?:=+|-+) *$/.test(nextLine)
              && execAt(BLOCK.lheading, `${line}\n${nextLine}`, 0);
            const continuation = setextContinuation
              ? `    ${nextLineWithoutTabs.replace(/^ {0,3}/, '')}`
              : nextLine;
            itemContents += '\n' + continuation;
          }

          blankLine = !nextLine.trim();
          p = lineEnd === -1 ? src.length : lineEnd + 1;
          line = nextLineWithoutTabs.slice(indent);
        }
      }

      // The loops above appended a '\n' the source may not have had. It
      // could only land on the item that exhausts src, whose raw is trimmed
      // below, and after which nothing reads endsWithBlankLine.
      const raw = src.slice(itemStart, p);

      if (!list.loose) {
        // If the previous item ended with a blank line, the list is loose.
        if (endsWithBlankLine) {
          list.loose = true;
        } else if (O.doubleBlankLine.test(raw)) {
          endsWithBlankLine = true;
        }
      }

      list.items.push({
        type: 'list_item',
        raw,
        task: !!O.listIsTask.test(itemContents),
        loose: false,
        text: itemContents,
        tokens: [],
      });
    }

    // Do not consume newlines at end of final item.
    const lastItem = list.items.at(-1);
    if (lastItem) {
      lastItem.raw = lastItem.raw.trimEnd();
      lastItem.text = lastItem.text.trimEnd();
    } else {
      // Not a list since there were no items.
      return;
    }
    list.raw = src.slice(listStart, p).trimEnd();

    // Item child tokens handled here at end because we needed to have the
    // final item to trim it first. First pass: tokenize items and finalize
    // list.loose from spacers before placing checkboxes.
    for (const item of list.items) {
      this.lexer.state.top = false;
      item.tokens = this.lexer.blockTokens(item.text, []);

      if (!list.loose) {
        const spacers = item.tokens.filter((t) => t.type === 'space');
        const hasMultipleLineBreaks = spacers.length > 0 && spacers.some((t) => O.anyLine.test(t.raw));
        list.loose = hasMultipleLineBreaks;
      }
    }

    // Second pass: place task checkboxes using the final list.loose.
    for (const item of list.items) {
      const itemToken = item.tokens[0];
      if (item.task && (itemToken?.type === 'text' || itemToken?.type === 'paragraph')) {
        item.text = item.text.replace(O.listReplaceTask, '');
        itemToken.raw = itemToken.raw.replace(O.listReplaceTask, '');
        itemToken.text = itemToken.text.replace(O.listReplaceTask, '');
        for (let i = this.lexer.inlineQueue.length - 1; i >= 0; i--) {
          if (O.listIsTask.test(this.lexer.inlineQueue[i].src)) {
            this.lexer.inlineQueue[i].src = this.lexer.inlineQueue[i].src.replace(O.listReplaceTask, '');
            break;
          }
        }

        const taskRaw = O.listTaskCheckbox.exec(item.raw);
        if (taskRaw) {
          const checkboxToken = {
            type: 'checkbox',
            raw: taskRaw[0] + ' ',
            checked: taskRaw[0] !== '[ ]',
          };
          item.checked = checkboxToken.checked;
          if (list.loose) {
            if (item.tokens[0] && ['paragraph', 'text'].includes(item.tokens[0].type) && 'tokens' in item.tokens[0] && item.tokens[0].tokens) {
              item.tokens[0].raw = checkboxToken.raw + item.tokens[0].raw;
              item.tokens[0].text = checkboxToken.raw + item.tokens[0].text;
              item.tokens[0].tokens.unshift(checkboxToken);
            } else {
              item.tokens.unshift({
                type: 'paragraph',
                raw: checkboxToken.raw,
                text: checkboxToken.raw,
                tokens: [checkboxToken],
              });
            }
          } else {
            item.tokens.unshift(checkboxToken);
          }
        }
      } else if (item.task) {
        item.task = false;
      }
    }

    // Set all items to loose if list is loose.
    if (list.loose) {
      for (const item of list.items) {
        item.loose = true;
        for (const token of item.tokens) {
          if (token.type === 'text') {
            token.type = 'paragraph';
          }
        }
      }
    }

    return list;
  }

  html(src, pos) {
    const cap = execAt(BLOCK.html, src, pos);
    if (cap) {
      const raw = trimTrailingBlankLines(cap[0]);
      return {
        type: 'html',
        block: true,
        raw,
        pre: cap[1] === 'pre' || cap[1] === 'script' || cap[1] === 'style',
        text: raw,
      };
    }
  }

  def(src, pos) {
    const cap = execAt(BLOCK.def, src, pos);
    if (cap) {
      // Outside angle brackets a link destination holds only balanced
      // parentheses.
      if (!O.startAngleBracket.test(cap[2]) && findClosingBracket(cap[2], '()') !== -1) {
        return;
      }
      const tag = normalizeLabel(cap[1]);
      const href = cap[2] ? cap[2].replace(O.hrefBrackets, '$1').replace(INLINE.anyPunctuation, '$1') : '';
      const title = cap[3] ? cap[3].substring(1, cap[3].length - 1).replace(INLINE.anyPunctuation, '$1') : cap[3];
      return {
        type: 'def',
        tag,
        raw: rtrim(cap[0], '\n'),
        href,
        title,
      };
    }
  }

  table(src, pos) {
    const cap = execAt(BLOCK.table, src, pos);
    if (!cap) {
      return;
    }
    if (!O.tableDelimiter.test(cap[2])) {
      // Delimiter row must have a pipe (|) or colon (:), otherwise it is a
      // setext heading.
      return;
    }
    const headers = splitCells(cap[1]);
    const aligns = cap[2].replace(O.tableAlignChars, '').split('|');
    const rows = cap[3]?.trim() ? cap[3].replace(O.tableRowBlankLine, '').split('\n') : [];

    const item = {
      type: 'table',
      raw: rtrim(cap[0], '\n'),
      header: [],
      align: [],
      rows: [],
    };

    if (headers.length !== aligns.length) {
      // Header and align columns must be equal; rows can be different.
      return;
    }

    for (const align of aligns) {
      if (O.tableAlignRight.test(align)) {
        item.align.push('right');
      } else if (O.tableAlignCenter.test(align)) {
        item.align.push('center');
      } else if (O.tableAlignLeft.test(align)) {
        item.align.push('left');
      } else {
        item.align.push(null);
      }
    }

    for (let i = 0; i < headers.length; i++) {
      item.header.push({
        text: headers[i],
        tokens: this.lexer.inline(headers[i]),
        header: true,
        align: item.align[i],
      });
    }

    for (const row of rows) {
      item.rows.push(splitCells(row, item.header.length).map((cell, i) => ({
        text: cell,
        tokens: this.lexer.inline(cell),
        header: false,
        align: item.align[i],
      })));
    }

    return item;
  }

  lheading(src, pos) {
    const cap = execAt(BLOCK.lheading, src, pos);
    if (cap) {
      const text = cap[1].trim();
      return {
        type: 'heading',
        raw: rtrim(cap[0], '\n'),
        depth: cap[2].charAt(0) === '=' ? 1 : 2,
        text,
        tokens: this.lexer.inline(text),
      };
    }
  }

  paragraph(src, pos) {
    const cap = execAt(BLOCK.paragraph, src, pos);
    if (cap) {
      const text = cap[1].charAt(cap[1].length - 1) === '\n'
        ? cap[1].slice(0, -1)
        : cap[1];
      return {
        type: 'paragraph',
        raw: cap[0],
        text,
        tokens: this.lexer.inline(text),
      };
    }
  }

  text(src, pos) {
    const cap = execAt(BLOCK.text, src, pos);
    if (cap) {
      return {
        type: 'text',
        raw: cap[0],
        text: cap[0],
        tokens: this.lexer.inline(cap[0]),
      };
    }
  }

  escape(src, pos) {
    const cap = execAt(INLINE.escape, src, pos);
    if (cap) {
      return { type: 'escape', raw: cap[0], text: cap[1] };
    }
  }

  tag(src, pos) {
    const cap = execAt(INLINE.tag, src, pos);
    if (cap) {
      if (!this.lexer.state.inLink && O.startATag.test(cap[0])) {
        this.lexer.state.inLink = true;
      } else if (this.lexer.state.inLink && O.endATag.test(cap[0])) {
        this.lexer.state.inLink = false;
      }
      if (!this.lexer.state.inRawBlock && O.startPreScriptTag.test(cap[0])) {
        this.lexer.state.inRawBlock = true;
      } else if (this.lexer.state.inRawBlock && O.endPreScriptTag.test(cap[0])) {
        this.lexer.state.inRawBlock = false;
      }
      return {
        type: 'html',
        raw: cap[0],
        inLink: this.lexer.state.inLink,
        inRawBlock: this.lexer.state.inRawBlock,
        block: false,
        text: cap[0],
      };
    }
  }

  link(src, pos) {
    // The link regex backtracks quadratically over unterminated-link inputs
    // like '[a](b'.repeat(n): at every '[' its greedy unquoted-href run
    // re-partitions the whole remainder while hunting for a ')' that never
    // comes. inlineTokens anchors one paren scan per run in
    // state.linkParenPossible; when it is false the regex cannot match, so
    // bail out before running it.
    if (this.lexer.state.linkParenPossible === false) {
      return;
    }
    const cap = execAt(INLINE.link, src, pos);
    if (cap) {
      const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
      if (isLabelEndInsideToken(src, pos, cap[1], labelStart)) {
        return;
      }
      const trimmedUrl = cap[2].trim();
      if (O.startAngleBracket.test(trimmedUrl)) {
        // CommonMark requires matching angle brackets.
        if (!O.endAngleBracket.test(trimmedUrl)) {
          return;
        }
        // Ending angle bracket cannot be escaped.
        const rtrimSlash = rtrim(trimmedUrl.slice(0, -1), '\\');
        if ((trimmedUrl.length - rtrimSlash.length) % 2 === 0) {
          return;
        }
      } else {
        // Find closing parenthesis.
        const lastParenIndex = findClosingBracket(cap[2], '()');
        if (lastParenIndex === -2) {
          // More open parens than closed.
          return;
        }
        if (lastParenIndex > -1) {
          const start = cap[0].indexOf('!') === 0 ? 5 : 4;
          const linkLen = start + cap[1].length + lastParenIndex;
          cap[2] = cap[2].substring(0, lastParenIndex);
          cap[0] = cap[0].substring(0, linkLen).trim();
          cap[3] = '';
        }
      }
      // The ')' that ends the match is the link closer only when it is not
      // escaped. `[foo](/url\)` has no closer; that paren is destination text.
      const unescaped = rtrim(cap[0].slice(0, -1), '\\');
      if ((cap[0].length - unescaped.length) % 2 === 0) {
        return;
      }
      let href = cap[2];
      const title = cap[3] ? cap[3].slice(1, -1) : '';
      href = href.trim();
      if (O.startAngleBracket.test(href)) {
        href = href.slice(1, -1);
      }
      return outputLink(cap, {
        href: href ? href.replace(INLINE.anyPunctuation, '$1') : href,
        title: title ? title.replace(INLINE.anyPunctuation, '$1') : title,
      }, cap[0], this.lexer);
    }
  }

  reflink(src, pos, links) {
    const cap = execAt(INLINE.reflink, src, pos) || execAt(INLINE.nolink, src, pos);
    if (cap) {
      const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
      if (isLabelEndInsideToken(src, pos, cap[1], labelStart)) {
        return;
      }
      const link = links[normalizeLabel(cap[2] || cap[1])];
      if (!link) {
        const text = cap[0].charAt(0);
        return { type: 'text', raw: text, text };
      }
      return outputLink(cap, link, cap[0], this.lexer);
    }
  }

  emStrong(src, pos, maskedSrc, prevChar = '') {
    let match = execAt(INLINE.emStrongLDelim, src, pos);
    if (!match) return;
    if (!match[1] && !match[2] && !match[3] && !match[4]) return;

    const delimChar = match[0][0];
    // A mid-run opener (for example the second star of an unmatched `**`)
    // must only pair with a delimiter that can only close, otherwise it
    // steals the opener of a later span.
    const midRun = prevChar === delimChar;

    // The start of this delimiter run may already be behind pos, either
    // taken as text after the whole run failed to match or used to close an
    // earlier span. Flanking and rules 9-10 are about the whole run, so find
    // its start.
    const srcStart = pos;
    let runStart = srcStart;
    while (runStart > 0 && maskedSrc[runStart - 1] === delimChar) {
      runStart--;
    }
    const runPrevChar = [...maskedSrc.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
    // The other delimiter character counts as punctuation here (`_**a*`).
    const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || !!INLINE.punctuation.exec(runPrevChar);
    if (runStart < srcStart) {
      prevChar = runPrevChar;
    }
    const prevPunct = runStart < srcStart ? runPrevPunct : !!INLINE.punctuation.exec(prevChar);

    // _ can't be between two alphanumerics.
    if (match[4] && prevChar.match(O.unicodeAlphaNumeric)) return;

    const nextChar = match[1] || match[3] || '';

    if (!nextChar || !prevChar || prevPunct) {
      // Unicode regex counts emoji as 1 char; spread into array for proper
      // count (used multiple times below).
      const lLength = [...match[0]].length - 1;
      let rDelim, rLength, delimTotal = lLength, midDelimTotal = 0;

      // Rules 9-10 count the whole run, and also apply when the opener could
      // close as well (`a*b**`, where `*` is both left- and right-flanking).
      const runLength = srcStart - runStart + lLength;
      const openerCanClose = !!runPrevChar.trim()
        && (!!nextChar || (delimChar === '*' && !runPrevPunct));
      if (delimChar !== '*' && delimChar !== '_') return;
      const endReg = delimChar === '*' ? INLINE.emStrongRDelimAst : INLINE.emStrongRDelimUnd;
      const lastPossibleEmStrongCloserIndex = cachedEmStrongCloserIndex(this, maskedSrc, delimChar);
      const emStrongCloserWindowStart = pos + lLength;
      if (lastPossibleEmStrongCloserIndex < emStrongCloserWindowStart) return;
      // Clip maskedSrc to same section of string as the remaining source.
      maskedSrc = maskedSrc.slice(pos + lLength);
      const lastPossibleEmStrongCloserIndexInWindow = lastPossibleEmStrongCloserIndex - emStrongCloserWindowStart;
      endReg.lastIndex = 0;

      while ((match = endReg.exec(maskedSrc)) !== null) {
        if (match.index > lastPossibleEmStrongCloserIndexInWindow) break;
        rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];

        if (!rDelim) continue; // Skip single * in __abc*abc__.

        rLength = [...rDelim].length;

        if (match[3] || match[4]) {
          // Found another left delimiter.
          delimTotal += rLength;
          continue;
        } else if (match[5] || match[6] || openerCanClose) {
          // Either left or right delimiter.
          if (midRun && (match[5] || match[6])) {
            // A mid-run opener cannot close against an ambiguous delimiter
            // that can also open; that delimiter opens its own span instead.
            break;
          }
          if (runLength % 3 && !((runLength + rLength) % 3)) {
            midDelimTotal += rLength;
            continue; // CommonMark emphasis rules 9-10.
          }
        }

        delimTotal -= rLength;

        if (delimTotal > 0) continue; // Haven't found enough closing delimiters.

        // Remove extra characters. *a*** -> *a*
        rLength = Math.min(rLength, rLength + delimTotal + midDelimTotal);
        // Char length can be >1 for unicode characters.
        const lastCharLength = [...match[0]][0].length;
        const raw = src.slice(pos, pos + lLength + match.index + lastCharLength + rLength);

        // Create `em` if smallest delimiter has odd char count. *a***
        if (Math.min(lLength, rLength) % 2) {
          const text = raw.slice(1, -1);
          return {
            type: 'em',
            raw,
            text,
            tokens: this.lexer.inlineTokens(text),
          };
        }

        // Create 'strong' if smallest delimiter has even char count. **a***
        const text = raw.slice(2, -2);
        return {
          type: 'strong',
          raw,
          text,
          tokens: this.lexer.inlineTokens(text),
        };
      }
    }
  }

  codespan(src, pos) {
    const cap = execAt(INLINE.code, src, pos);
    if (cap) {
      let text = cap[2].replace(O.newLineCharGlobal, ' ');
      const hasNonSpaceChars = O.nonSpaceChar.test(text);
      const hasSpaceCharsOnBothEnds = O.startingSpaceChar.test(text) && O.endingSpaceChar.test(text);
      if (hasNonSpaceChars && hasSpaceCharsOnBothEnds) {
        text = text.substring(1, text.length - 1);
      }
      return { type: 'codespan', raw: cap[0], text };
    }
  }

  br(src, pos) {
    const cap = execAt(INLINE.br, src, pos);
    if (cap) {
      return { type: 'br', raw: cap[0] };
    }
  }

  del(src, pos, maskedSrc, prevChar = '') {
    let match = execAt(INLINE.delLDelim, src, pos);
    if (!match) return;

    const nextChar = match[1] || '';

    if (!nextChar || !prevChar || INLINE.punctuation.exec(prevChar)) {
      // Unicode regex counts emoji as 1 char; spread into array for proper
      // count.
      const lLength = [...match[0]].length - 1;
      let rDelim, rLength, delimTotal = lLength;

      const endReg = INLINE.delRDelim;
      const lastPossibleDelCloserIndex = cachedDelCloserIndex(this, maskedSrc);
      const delCloserWindowStart = pos + lLength;
      if (lastPossibleDelCloserIndex < delCloserWindowStart) return;
      // Clip maskedSrc to same section of string as the remaining source.
      maskedSrc = maskedSrc.slice(pos + lLength);
      const lastPossibleDelCloserIndexInWindow = lastPossibleDelCloserIndex - delCloserWindowStart;
      endReg.lastIndex = 0;

      while ((match = endReg.exec(maskedSrc)) !== null) {
        if (match.index > lastPossibleDelCloserIndexInWindow) break;
        rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];

        if (!rDelim) continue;

        rLength = [...rDelim].length;

        if (rLength !== lLength) continue;

        if (match[3] || match[4]) {
          // Found another left delimiter.
          delimTotal += rLength;
          continue;
        }

        delimTotal -= rLength;

        if (delimTotal > 0) continue; // Haven't found enough closing delimiters.

        // Remove extra characters.
        rLength = Math.min(rLength, rLength + delimTotal);
        // Char length can be >1 for unicode characters.
        const lastCharLength = [...match[0]][0].length;
        const raw = src.slice(pos, pos + lLength + match.index + lastCharLength + rLength);

        // Create del token — only single ~ or double ~~ supported.
        const text = raw.slice(lLength, -lLength);
        return {
          type: 'del',
          raw,
          text,
          tokens: this.lexer.inlineTokens(text),
        };
      }
    }
  }

  autolink(src, pos) {
    const cap = execAt(INLINE.autolink, src, pos);
    if (cap) {
      let text, href;
      if (cap[2] === '@') {
        text = cap[1];
        href = 'mailto:' + text;
      } else {
        text = cap[1];
        href = text;
      }
      return {
        type: 'link',
        raw: cap[0],
        text,
        href,
        autolink: true,
        tokens: [{ type: 'text', raw: text, text }],
      };
    }
  }

  url(src, pos) {
    let cap;
    if (cap = execAt(INLINE.url, src, pos)) {
      let text, href;
      if (cap[2] === '@') {
        text = cap[0];
        href = 'mailto:' + text;
      } else {
        // Do extended autolink path validation.
        let prevCapZero;
        do {
          prevCapZero = cap[0];
          cap[0] = INLINE._backpedal.exec(cap[0])?.[0] ?? '';
        } while (prevCapZero !== cap[0]);
        text = cap[0];
        if (cap[1] === 'www.') {
          href = 'http://' + cap[0];
        } else {
          href = cap[0];
        }
      }
      return {
        type: 'link',
        raw: cap[0],
        text,
        href,
        autolink: true,
        tokens: [{ type: 'text', raw: text, text }],
      };
    }
  }

  inlineText(src, pos) {
    const cap = execAt(INLINE.text, src, pos);
    if (cap) {
      const escaped = this.lexer.state.inRawBlock;
      return {
        type: 'text',
        raw: cap[0],
        // Raw HTML keeps whatever it was written with; everywhere else a
        // numeric character reference stands for the character itself.
        text: escaped ? cap[0] : decodeNumericCharacterReferences(cap[0]),
        escaped,
      };
    }
  }
}

/* ------------------------------------------------------------------ */
/* Lexer — block and inline tokenization over one string with an index. */
/* ------------------------------------------------------------------ */

function isUrlStartChar(ch) {
  if (!ch) return false;
  const code = ch.charCodeAt(0);
  return (code >= 48 && code <= 57) // 0-9
    || (code >= 65 && code <= 90) // A-Z
    || (code >= 97 && code <= 122) // a-z
    || ch === '.' || ch === '_' || ch === '+' || ch === '-';
}

class Lexer {
  constructor() {
    this.tokens = [];
    this.tokens.links = Object.create(null);
    this.tokenizer = new Tokenizer();
    this.tokenizer.lexer = this;
    this.inlineQueue = [];
    this.state = {
      inLink: false,
      inRawBlock: false,
      linkEmitted: false,
      linkParenPossible: true,
      top: true,
    };
  }

  static lex(src) {
    const lexer = new Lexer();
    return lexer.lex(src);
  }

  lex(src) {
    src = src.replace(O.carriageReturn, '\n');
    this.blockTokens(src, this.tokens);
    for (let i = 0; i < this.inlineQueue.length; i++) {
      const next = this.inlineQueue[i];
      // An inline <pre>, <code>, <kbd> or <script> left open ends with the
      // block holding it; carried over, it would stop every later block's
      // text from being escaped.
      this.state.inRawBlock = false;
      this.inlineTokens(next.src, next.tokens);
    }
    this.inlineQueue = [];
    return this.tokens;
  }

  blockTokens(src, tokens = [], lastParagraphClipped = false) {
    let pos = 0;
    const end = src.length;
    let srcLength = Infinity;
    while (pos < end) {
      if (end - pos < srcLength) {
        srcLength = end - pos;
      } else {
        this.infiniteLoopError(src.charCodeAt(pos));
        break;
      }

      let token;

      // Newline (blank lines).
      if (token = this.tokenizer.space(src, pos)) {
        pos += token.raw.length;
        const lastToken = tokens.at(-1);
        if (token.raw.length === 1 && lastToken !== undefined) {
          // A single \n as a spacer terminates the last line, so move it
          // there instead of making an unnecessary paragraph tag.
          lastToken.raw += '\n';
        } else {
          tokens.push(token);
        }
        continue;
      }

      // First-character dispatch: count the leading spaces (up to 4) and
      // look at the first real character. Only the block tokenizers that
      // can match there are tried, in marked's own order.
      let p = pos;
      let spaces = 0;
      while (spaces < 4 && src[p] === ' ') {
        p++;
        spaces++;
      }
      const indented = spaces >= 4;
      const first = src[p];

      // Indented code.
      if ((indented || (!indented && first === '\t'))
        && (token = this.tokenizer.code(src, pos))) {
        pos += token.raw.length;
        const lastToken = tokens.at(-1);
        // An indented code block cannot interrupt a paragraph.
        if (lastToken?.type === 'paragraph' || lastToken?.type === 'text') {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.text;
          this.inlineQueue.at(-1).src = lastToken.text;
        } else {
          tokens.push(token);
        }
        continue;
      }

      // Fenced code.
      if (!indented && first === '`' && src[p + 1] === '`' && src[p + 2] === '`'
        && (token = this.tokenizer.fences(src, pos))) {
        pos += token.raw.length;
        tokens.push(token);
        continue;
      }
      if (!indented && first === '~' && src[p + 1] === '~' && src[p + 2] === '~'
        && (token = this.tokenizer.fences(src, pos))) {
        pos += token.raw.length;
        tokens.push(token);
        continue;
      }

      // ATX heading.
      if (!indented && first === '#'
        && (token = this.tokenizer.heading(src, pos))) {
        pos += token.raw.length;
        tokens.push(token);
        continue;
      }

      // Thematic break.
      if (!indented && (first === '-' || first === '_' || first === '*')
        && (token = this.tokenizer.hr(src, pos))) {
        pos += token.raw.length;
        tokens.push(token);
        continue;
      }

      // Blockquote.
      if (!indented && first === '>'
        && (token = this.tokenizer.blockquote(src, pos))) {
        pos += token.raw.length;
        tokens.push(token);
        continue;
      }

      // List.
      if (!indented && (first === '*' || first === '+' || first === '-'
          || (first >= '0' && first <= '9'))
        && (token = this.tokenizer.list(src, pos))) {
        pos += token.raw.length;
        tokens.push(token);
        continue;
      }

      // HTML block.
      if (!indented && first === '<'
        && (token = this.tokenizer.html(src, pos))) {
        pos += token.raw.length;
        tokens.push(token);
        continue;
      }

      // Link reference definition.
      if (!indented && first === '['
        && (token = this.tokenizer.def(src, pos))) {
        pos += token.raw.length;
        const lastToken = tokens.at(-1);
        if (lastToken?.type === 'paragraph' || lastToken?.type === 'text') {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.raw;
          this.inlineQueue.at(-1).src = lastToken.text;
        } else {
          // The first definition of a label wins, but a later one still
          // consumes its text.
          if (!this.tokens.links[token.tag]) {
            this.tokens.links[token.tag] = {
              href: token.href,
              title: token.title,
            };
          }
          tokens.push(token);
        }
        continue;
      }

      // Table (GFM).
      if (token = this.tokenizer.table(src, pos)) {
        pos += token.raw.length;
        tokens.push(token);
        continue;
      }

      // Setext heading.
      if (token = this.tokenizer.lheading(src, pos)) {
        pos += token.raw.length;
        tokens.push(token);
        continue;
      }

      // Top-level paragraph.
      if (this.state.top && (token = this.tokenizer.paragraph(src, pos))) {
        const lastToken = tokens.at(-1);
        if (lastParagraphClipped && lastToken?.type === 'paragraph') {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.text;
          this.inlineQueue.pop();
          this.inlineQueue.at(-1).src = lastToken.text;
        } else {
          tokens.push(token);
        }
        lastParagraphClipped = false; // no extensions: nothing clips a paragraph
        pos += token.raw.length;
        continue;
      }

      // Text (a single line that is none of the above).
      if (token = this.tokenizer.text(src, pos)) {
        pos += token.raw.length;
        const lastToken = tokens.at(-1);
        if (lastToken?.type === 'text') {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.text;
          this.inlineQueue.pop();
          this.inlineQueue.at(-1).src = lastToken.text;
        } else {
          tokens.push(token);
        }
        continue;
      }

      if (pos < end) {
        this.infiniteLoopError(src.charCodeAt(pos));
        break;
      }
    }

    this.state.top = true;
    return tokens;
  }

  inline(src, tokens = []) {
    this.inlineQueue.push({ src, tokens });
    return tokens;
  }

  // Does this link text hold a link already? An image does not count: an
  // image may hold a link, a link may not.
  linkInText(text) {
    if (!text.includes('[')) {
      return false;
    }
    for (const match of text.matchAll(INLINE.blockSkip)) {
      // blockSkip also matches code spans and html, and the `!` of an image
      // is left out of the match, so read the character before it.
      if (execAt(INLINE.link, match[0], 0) && text.charAt(match.index - 1) !== '!') {
        return true;
      }
    }
    for (const match of text.matchAll(INLINE.reflinkSearch)) {
      const match0 = match[0];
      const refStart = match0.lastIndexOf('[');
      if (match0.charAt(0) === '!' || !Object.hasOwn(this.tokens.links, normalizeLabel(match0.slice(refStart + 1, -1)))) {
        continue;
      }
      // A candidate holding a link is not a link either, so it does not count.
      if (refStart > 1 && this.linkInText(match0.slice(1, refStart - 1))) {
        continue;
      }
      return true;
    }
    return false;
  }

  inlineTokens(src, tokens = []) {
    // One paren scan per inline run, shared with Tokenizer.link: without a
    // ')' ahead the link regex cannot match, and skipping it avoids its
    // quadratic backtracking over unterminated-link inputs.
    const prevLinkParenPossible = this.state.linkParenPossible;
    this.state.linkParenPossible = prevLinkParenPossible && src.includes(')');
    try {
      return this._inlineTokensInner(src, tokens);
    } finally {
      // A nested run (e.g. a link label) anchored on its own substring;
      // restore the outer run's flag for the rest of its loop.
      this.state.linkParenPossible = prevLinkParenPossible;
    }
  }

  _inlineTokensInner(src, tokens) {
    // The masked source is only read by emStrong and del, which need a *,
    // _ or ~ to start. Skip building it for a run without one.
    const hasEmDel = src.includes('*') || src.includes('_') || src.includes('~');
    const maskedSrc = hasEmDel ? this._maskSrc(src) : src;

    // One scan of this maskedSrc for the last emphasis, strong, and
    // strikethrough closers, shared by every opener in the pass. Only
    // needed when such a delimiter exists at all.
    if (hasEmDel) {
      beginCloserScan(this.tokenizer, maskedSrc);
      try {
        return this._tokenizeInlines(src, maskedSrc, tokens);
      } finally {
        endCloserScan(this.tokenizer);
      }
    }
    return this._tokenizeInlines(src, maskedSrc, tokens);
  }

  _tokenizeInlines(src, maskedSrc, tokens) {
    let keepPrevChar = false;
    let prevChar = '';
    let pos = 0;
    const end = src.length;
    let srcLength = Infinity;
    // One scan per run for '@': an email autolink can only start where one
    // is, so runs without it never try the url tokenizer for word starts.
    const hasAt = src.includes('@');
    while (pos < end) {
      if (end - pos < srcLength) {
        srcLength = end - pos;
      } else {
        this.infiniteLoopError(src.charCodeAt(pos));
        break;
      }

      if (!keepPrevChar) {
        prevChar = '';
      }
      keepPrevChar = false;

      let token;
      const ch = src[pos];

      // First-character dispatch: only the tokenizers that can match at
      // this character are tried, in marked's own order. Anything else can
      // only be plain text.
      if (ch === '\\') {
        if (token = this.tokenizer.escape(src, pos)) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
        // A backslash-newline is a hard break, not an escape.
        if (token = this.tokenizer.br(src, pos)) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
      } else if (ch === '<') {
        if (token = this.tokenizer.tag(src, pos)) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
        if (token = this.tokenizer.autolink(src, pos)) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
      } else if (ch === '[' || (ch === '!' && src[pos + 1] === '[')) {
        if (token = this.tokenizer.link(src, pos)) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
        if (token = this.tokenizer.reflink(src, pos, this.tokens.links)) {
          pos += token.raw.length;
          const lastToken = tokens.at(-1);
          if (token.type === 'text' && lastToken?.type === 'text') {
            lastToken.raw += token.raw;
            lastToken.text += token.text;
          } else {
            tokens.push(token);
          }
          continue;
        }
      } else if (ch === '*' || ch === '_') {
        if (token = this.tokenizer.emStrong(src, pos, maskedSrc, prevChar)) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
        // An email local part may start with `_` (e.g. `__a@b.com`): when
        // emphasis fails, the url tokenizer still claims the whole address.
        if (ch === '_' && hasAt && !this.state.inLink
          && (token = this.tokenizer.url(src, pos))) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
      } else if (ch === '`') {
        if (token = this.tokenizer.codespan(src, pos)) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
      } else if (ch === ' ') {
        if (token = this.tokenizer.br(src, pos)) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
      } else if (ch === '~') {
        if (token = this.tokenizer.del(src, pos, maskedSrc, prevChar)) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
      } else if (ch === 'h' || ch === 'H' || ch === 'f' || ch === 'F' || ch === 'w'
        || (hasAt && isUrlStartChar(ch))) {
        if (!this.state.inLink && (token = this.tokenizer.url(src, pos))) {
          pos += token.raw.length;
          tokens.push(token);
          continue;
        }
      }

      // Plain text.
      if (token = this.tokenizer.inlineText(src, pos)) {
        pos += token.raw.length;
        // Track prevChar before a string of ____ started.
        if (token.raw.slice(-1) !== '_') {
          prevChar = token.raw.slice(-1);
        }
        keepPrevChar = true;
        const lastToken = tokens.at(-1);
        if (lastToken?.type === 'text') {
          lastToken.raw += token.raw;
          lastToken.text += token.text;
        } else {
          tokens.push(token);
        }
        continue;
      }

      if (pos < end) {
        this.infiniteLoopError(src.charCodeAt(pos));
        break;
      }
    }

    return tokens;
  }

  // Mask links, code, html and escapes so emStrong and del do not see their
  // delimiters inside them.
  _maskSrc(src) {
    let maskedSrc = src;

    // Mask out reflinks.
    if (this.tokens.links && src.includes('[')) {
      const reflinkSearch = INLINE.reflinkSearch;
      const maskReflink = (match0) => {
        const refStart = match0.lastIndexOf('[');
        if (!Object.hasOwn(this.tokens.links, normalizeLabel(match0.slice(refStart + 1, -1)))) {
          return match0;
        }
        // CommonMark: "Links may not contain other links, at any level of
        // nesting." A candidate whose text already holds one never becomes
        // a link, so flattening the whole span would hide the emphasis that
        // does still apply inside it. Mask the links it holds instead.
        // Images are exempt: their text is flattened into an alt attribute.
        if (refStart > 1 && match0.charAt(0) !== '!') {
          const text = match0.slice(1, refStart - 1);
          if (this.linkInText(text)) {
            return '[' + text.replace(reflinkSearch, maskReflink)
              + '][' + 'a'.repeat(match0.length - refStart - 2) + ']';
          }
        }
        return '[' + 'a'.repeat(match0.length - 2) + ']';
      };
      maskedSrc = maskedSrc.replace(reflinkSearch, maskReflink);
    }

    // Mask out escaped characters. Every mask must keep the length it
    // replaces: emStrong and del line maskedSrc up with src by slicing
    // from the end. A backslash inside a code span is literal, not an
    // escape. Mask the backticks inside the span instead, so blockSkip
    // still skips all of it. The pattern only matches backticks and
    // backslash-escapes, so skip the pass when neither is present.
    if (maskedSrc.includes('`') || maskedSrc.includes('\\')) {
      maskedSrc = maskedSrc.replace(INLINE.anyPunctuationOutsideCode, (match0, code, punct) => {
        if (punct) {
          return '+'.repeat(match0.length);
        }
        if (code) {
          return code + match0.slice(code.length, -code.length).replace(/`/g, '+') + code;
        }
        return match0;
      });
    }

    // Mask out other blocks. blockSkip only matches links, code spans and
    // `<...>` html, so skip the pass when none of their openers is present.
    if (maskedSrc.includes('[') || maskedSrc.includes('`') || maskedSrc.includes('<')) {
      maskedSrc = maskedSrc.replace(INLINE.blockSkip, (match0, _link, context) => {
        const offset = context ? context.length : 0;
        return match0.slice(0, offset) + '[' + 'a'.repeat(match0.length - offset - 2) + ']';
      });
    }

    return maskedSrc;
  }

  infiniteLoopError(byte) {
    throw new Error('Infinite loop on byte: ' + byte);
  }
}

/* ------------------------------------------------------------------ */
/* Renderer — turns tokens into HTML.                                  */
/* ------------------------------------------------------------------ */

class Renderer {
  constructor() {
    this.parser = null;
  }

  space() {
    return '';
  }

  code({ text, lang, escaped }) {
    const langString = (lang || '').match(O.notSpaceStart)?.[0];
    // An empty code block has no content, so it must not gain a newline.
    const code = text ? text.replace(O.endingNewline, '') + '\n' : '';
    if (!langString) {
      return '<pre><code>'
        + (escaped ? code : escapeHtmlEntities(code, true))
        + '</code></pre>\n';
    }
    return '<pre><code class="language-'
      + escapeHtmlEntities(langString)
      + '">'
      + (escaped ? code : escapeHtmlEntities(code, true))
      + '</code></pre>\n';
  }

  blockquote({ tokens }) {
    const body = this.parser.parse(tokens);
    return `<blockquote>\n${body}</blockquote>\n`;
  }

  html({ text }) {
    return text;
  }

  def() {
    return '';
  }

  heading({ tokens, depth }) {
    return `<h${depth}>${this.parser.parseInline(tokens)}</h${depth}>\n`;
  }

  hr() {
    return '<hr>\n';
  }

  list(token) {
    const ordered = token.ordered;
    const start = token.start;
    let body = '';
    for (let j = 0; j < token.items.length; j++) {
      body += this.listitem(token.items[j]);
    }
    const type = ordered ? 'ol' : 'ul';
    const startAttr = (ordered && start !== 1) ? (' start="' + start + '"') : '';
    return '<' + type + startAttr + '>\n' + body + '</' + type + '>\n';
  }

  listitem(item) {
    return `<li>${this.parser.parse(item.tokens)}</li>\n`;
  }

  checkbox({ checked }) {
    return '<input '
      + (checked ? 'checked="" ' : '')
      + 'disabled="" type="checkbox"> ';
  }

  paragraph({ tokens }) {
    return `<p>${this.parser.parseInline(tokens)}</p>\n`;
  }

  table(token) {
    let header = '';
    let cell = '';
    for (let j = 0; j < token.header.length; j++) {
      cell += this.tablecell(token.header[j]);
    }
    header += this.tablerow({ text: cell });

    let body = '';
    for (let j = 0; j < token.rows.length; j++) {
      const row = token.rows[j];
      cell = '';
      for (let k = 0; k < row.length; k++) {
        cell += this.tablecell(row[k]);
      }
      body += this.tablerow({ text: cell });
    }
    if (body) body = `<tbody>${body}</tbody>`;

    return '<table>\n'
      + '<thead>\n'
      + header
      + '</thead>\n'
      + body
      + '</table>\n';
  }

  tablerow({ text }) {
    return `<tr>\n${text}</tr>\n`;
  }

  tablecell(token) {
    const content = this.parser.parseInline(token.tokens);
    const type = token.header ? 'th' : 'td';
    const tag = token.align
      ? `<${type} align="${token.align}">`
      : `<${type}>`;
    return tag + content + `</${type}>\n`;
  }

  strong({ tokens }) {
    return `<strong>${this.parser.parseInline(tokens)}</strong>`;
  }

  em({ tokens }) {
    return `<em>${this.parser.parseInline(tokens)}</em>`;
  }

  codespan({ text }) {
    return `<code>${escapeHtmlEntities(text, true)}</code>`;
  }

  br() {
    return '<br>';
  }

  del({ tokens }) {
    return `<del>${this.parser.parseInline(tokens)}</del>`;
  }

  link({ href, title, text, tokens, autolink }) {
    // References are not resolved inside an autolink, so every `&` there is
    // literal. Elsewhere only an `&` that cannot start one needs escaping.
    const parsedText = autolink
      ? escapeHtmlEntities(text, true)
      : this.parser.parseInline(tokens);
    const cleanHref = cleanUrl(href);
    if (cleanHref === null) {
      return parsedText;
    }
    href = escapeHtmlEntities(cleanHref, autolink);
    let out = '<a href="' + href + '"';
    if (title) {
      out += ' title="' + (escapeHtmlEntities(title)) + '"';
    }
    out += '>' + parsedText + '</a>';
    return out;
  }

  image({ href, title, text, tokens }) {
    if (tokens) {
      text = this.parser.parseInline(tokens, this.parser.textRenderer);
    }
    const cleanHref = cleanUrl(href);
    if (cleanHref === null) {
      return escapeHtmlEntities(text);
    }
    href = cleanHref;
    let out = `<img src="${escapeHtmlEntities(href)}" alt="${escapeHtmlEntities(text)}"`;
    if (title) {
      out += ` title="${escapeHtmlEntities(title)}"`;
    }
    out += '>';
    return out;
  }

  text(token) {
    return 'tokens' in token && token.tokens
      ? this.parser.parseInline(token.tokens)
      : ('escaped' in token && token.escaped ? token.text : escapeHtmlEntities(token.text));
  }
}

// TextRenderer — returns only the textual part of a token (used for image
// alt text, where no markup is allowed).
class TextRenderer {
  constructor() {
    this.parser = null;
  }

  strong({ text, tokens }) {
    return tokens ? this.parser.parseInline(tokens, this) : text;
  }

  em({ text, tokens }) {
    return tokens ? this.parser.parseInline(tokens, this) : text;
  }

  codespan({ text }) {
    return text;
  }

  del({ text, tokens }) {
    return tokens ? this.parser.parseInline(tokens, this) : text;
  }

  html({ text }) {
    return text;
  }

  text({ text }) {
    return text;
  }

  link({ text, tokens }) {
    return tokens ? this.parser.parseInline(tokens, this) : text;
  }

  image({ text, tokens }) {
    return tokens ? this.parser.parseInline(tokens, this) : text;
  }

  br() {
    return '';
  }

  checkbox({ raw }) {
    return raw;
  }
}

/* ------------------------------------------------------------------ */
/* Parser — walks the token tree and renders it.                       */
/* ------------------------------------------------------------------ */

class Parser {
  constructor() {
    this.renderer = new Renderer();
    this.renderer.parser = this;
    this.textRenderer = new TextRenderer();
    this.textRenderer.parser = this;
  }

  parse(tokens) {
    let out = '';
    for (let i = 0; i < tokens.length; i++) {
      const token = tokens[i];
      switch (token.type) {
        case 'space': out += this.renderer.space(token); break;
        case 'hr': out += this.renderer.hr(token); break;
        case 'heading': out += this.renderer.heading(token); break;
        case 'code': out += this.renderer.code(token); break;
        case 'table': out += this.renderer.table(token); break;
        case 'blockquote': out += this.renderer.blockquote(token); break;
        case 'list': out += this.renderer.list(token); break;
        case 'checkbox': out += this.renderer.checkbox(token); break;
        case 'html': out += this.renderer.html(token); break;
        case 'def': out += this.renderer.def(token); break;
        case 'paragraph': out += this.renderer.paragraph(token); break;
        case 'text': out += this.renderer.text(token); break;
        default: throw new Error('Token with "' + token.type + '" type was not found.');
      }
    }
    return out;
  }

  parseInline(tokens, renderer = this.renderer) {
    let out = '';
    for (let i = 0; i < tokens.length; i++) {
      const token = tokens[i];
      switch (token.type) {
        case 'escape': out += renderer.text(token); break;
        case 'html': out += renderer.html(token); break;
        case 'link': out += renderer.link(token); break;
        case 'image': out += renderer.image(token); break;
        case 'checkbox': out += renderer.checkbox(token); break;
        case 'strong': out += renderer.strong(token); break;
        case 'em': out += renderer.em(token); break;
        case 'codespan': out += renderer.codespan(token); break;
        case 'br': out += renderer.br(token); break;
        case 'del': out += renderer.del(token); break;
        case 'text': out += renderer.text(token); break;
        default: throw new Error('Token with "' + token.type + '" type was not found.');
      }
    }
    return out;
  }
}

/* ------------------------------------------------------------------ */
/* Entry point                                                         */
/* ------------------------------------------------------------------ */

// The HTML marked 18.1.3 renders for `markdown`, with marked's defaults
// (GFM on, breaks off, pedantic off, async off). Fresh lexer and parser
// per call: parse keeps nothing from an earlier call.
export function parse(markdown) {
  const lexer = new Lexer();
  const tokens = lexer.lex(markdown);
  const parser = new Parser();
  return parser.parse(tokens);
}
