// parse.js — fast CommonMark + GFM parser matching marked 18.1.3 defaults.
// Hand-written from the CommonMark 0.31.2 + GFM 0.29 specs and oracle probes
// against the vendored marked build. Dependency-free ES module.

const SP = 32, TAB = 9, LF = 10, CR = 13, FF = 12;

// ---------- character classification ----------
// ASCII punctuation (CommonMark): !"#$%&'()*+,-./:;<=>?@[\]^_`{|}~
function isAsciiPunct(c) {
  return (c >= 33 && c <= 47) || (c >= 58 && c <= 64) ||
    (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
}
// Unicode whitespace per CommonMark: tab LF FF CR space + Zs
function isWSCode(c) {
  return c === 9 || c === 10 || c === 12 || c === 13 || c === 32 ||
    c === 0xa0 || c === 0x1680 || (c >= 0x2000 && c <= 0x200a) ||
    c === 0x202f || c === 0x205f || c === 0x3000;
}
// Unicode punctuation: ASCII punct or general category P / S.
const punctRe = /[\p{P}\p{S}]/u;
const punctCache = new Map();
function isPunctStr(ch) {
  if (ch.length === 1) {
    const c = ch.charCodeAt(0);
    if (c < 128) return isAsciiPunct(c);
  }
  let v = punctCache.get(ch);
  if (v === undefined) { v = punctRe.test(ch); punctCache.set(ch, v); }
  return v;
}
function isPunctCode(c) {
  if (c < 128) return isAsciiPunct(c);
  return isPunctStr(String.fromCharCode(c));
}

// ---------- escaping ----------
// Plain escaper: escapes & < > " ' with NO entity handling (for code content).
function escRaw(s) {
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    let rep = null;
    if (c === 38) rep = '&amp;';
    else if (c === 60) rep = '&lt;';
    else if (c === 62) rep = '&gt;';
    else if (c === 34) rep = '&quot;';
    else if (c === 39) rep = '&#39;';
    if (rep !== null) {
      if (start < i) out += s.slice(start, i);
      out += rep;
      start = i + 1;
    }
  }
  if (start === 0) return s;
  if (start < s.length) out += s.slice(start);
  return out;
}
// Escaper for hrefs: valid entities (named AND numeric) pass through
// literally (no decoding); bare & becomes &amp;.
function escHrefKeep(s) {
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 38) {
      const eEnd = entityEnd(s, i);
      if (eEnd > 0) {
        if (start < i) out += s.slice(start, i);
        out += s.slice(i, eEnd);
        i = eEnd - 1;
        start = eEnd;
        continue;
      }
      if (start < i) out += s.slice(start, i);
      out += '&amp;';
      start = i + 1;
      continue;
    }
    let rep = null;
    if (c === 60) rep = '&lt;';
    else if (c === 62) rep = '&gt;';
    else if (c === 34) rep = '&quot;';
    else if (c === 39) rep = '&#39;';
    if (rep !== null) {
      if (start < i) out += s.slice(start, i);
      out += rep;
      start = i + 1;
    }
  }
  if (start === 0) return s;
  if (start < s.length) out += s.slice(start);
  return out;
}
function esc(s) {
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 38) {
      const eEnd = entityEnd(s, i);
      if (eEnd > 0) {
        if (s.charCodeAt(i + 1) === 35) {
          // numeric entity: decode, then escape the char if needed
          const d = decodeNumericEntity(s, i);
          const ch = d.ch;
          const cc = ch.charCodeAt(0);
          let rep = null;
          if (cc === 38) rep = '&amp;';
          else if (cc === 60) rep = '&lt;';
          else if (cc === 62) rep = '&gt;';
          else if (cc === 34) rep = '&quot;';
          else if (cc === 39) rep = '&#39;';
          if (start < i) out += s.slice(start, i);
          out += rep !== null ? rep : ch;
          i = eEnd - 1;
          start = eEnd;
        } else {
          // named entity: pass through literally
          if (start < i) out += s.slice(start, i);
          out += s.slice(i, eEnd);
          i = eEnd - 1;
          start = eEnd;
        }
        continue;
      }
      if (start < i) out += s.slice(start, i);
      out += '&amp;';
      start = i + 1;
      continue;
    }
    let rep = null;
    if (c === 60) rep = '&lt;';
    else if (c === 62) rep = '&gt;';
    else if (c === 34) rep = '&quot;';
    else if (c === 39) rep = '&#39;';
    if (rep !== null) {
      if (start < i) out += s.slice(start, i);
      out += rep;
      start = i + 1;
    }
  }
  if (start === 0) return s;
  if (start < s.length) out += s.slice(start);
  return out;
}

// Percent-encode an href like encodeURI does, then HTML-escape it.
// encodeURI leaves unreserved + ; , / ? : @ & = + $ - _ . ! ~ * ' ( ) # alone.
const HREF_SAFE = new Uint8Array(128);
(function () {
  const safe = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789;,/?:@&=+$-_.!~*\'()#%';
  for (let i = 0; i < safe.length; i++) HREF_SAFE[safe.charCodeAt(i)] = 1;
})();
const HEX = '0123456789ABCDEF';
function encodeHref(s, raw) {
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c < 128 && HREF_SAFE[c]) continue;
    if (start < i) out += s.slice(start, i);
    if (c < 128) {
      out += '%' + HEX[(c >> 4) & 15] + HEX[c & 15];
      start = i + 1;
    } else {
      // UTF-8 encode this code point (handles surrogate pairs).
      let cp = c;
      let adv = 1;
      if (c >= 0xd800 && c <= 0xdbff && i + 1 < s.length) {
        const lo = s.charCodeAt(i + 1);
        if (lo >= 0xdc00 && lo <= 0xdfff) { cp = 0x10000 + ((c - 0xd800) << 10) + (lo - 0xdc00); adv = 2; }
        else cp = 0xfffd;
      } else if (c >= 0xd800 && c <= 0xdfff) cp = 0xfffd;
      // emit UTF-8 bytes
      let bytes;
      if (cp < 0x80) bytes = [cp];
      else if (cp < 0x800) bytes = [0xc0 | (cp >> 6), 0x80 | (cp & 63)];
      else if (cp < 0x10000) bytes = [0xe0 | (cp >> 12), 0x80 | ((cp >> 6) & 63), 0x80 | (cp & 63)];
      else bytes = [0xf0 | (cp >> 18), 0x80 | ((cp >> 12) & 63), 0x80 | ((cp >> 6) & 63), 0x80 | (cp & 63)];
      for (let b = 0; b < bytes.length; b++) out += '%' + HEX[(bytes[b] >> 4) & 15] + HEX[bytes[b] & 15];
      i += adv - 1;
      start = i + 1;
    }
  }
  const escFn = raw ? escRaw : escHrefKeep;
  if (start === 0) return escFn(s);
  if (start < s.length) out += s.slice(start);
  return escFn(out);
}

// ---------- entities ----------
// Named entities are NOT decoded: any &word; (word = [A-Za-z0-9_]+) passes
// through literally. Only numeric entities are decoded (invalid -> U+FFFD).
function decodeNumericEntity(s, i) {
  // s[i] === '&', s[i+1] === '#'. Returns {ch, end} or null.
  let j = i + 2;
  let hex = false;
  if (j < s.length && (s[j] === 'x' || s[j] === 'X')) { hex = true; j++; }
  const ds = j;
  while (j < s.length) {
    const c = s.charCodeAt(j);
    if (hex ? ((c >= 48 && c <= 57) || (c >= 97 && c <= 102) || (c >= 65 && c <= 70)) : (c >= 48 && c <= 57)) j++;
    else break;
  }
  if (j === ds || j >= s.length || s[j] !== ';') return null;
  const digits = j - ds;
  if (hex ? digits > 6 : digits > 7) return null;
  let cp;
  if (hex) cp = parseInt(s.slice(ds, j), 16);
  else cp = parseInt(s.slice(ds, j), 10);
  if (!isFinite(cp) || cp === 0 || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) cp = 0xfffd;
  return { ch: String.fromCodePoint(cp), end: j + 1 };
}
// Is there an entity reference starting at s[i] ('&')? Returns end index or 0.
// Named: &\w+;  Numeric: &#digits; &#xhex; (must be valid digits to count).
function entityEnd(s, i) {
  if (s[i] !== '&') return 0;
  let j = i + 1;
  if (j < s.length && s[j] === '#') {
    const d = decodeNumericEntity(s, i);
    return d ? d.end : 0;
  }
  const n = s.length;
  while (j < n) {
    const c = s.charCodeAt(j);
    if ((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95) j++;
    else break;
  }
  if (j > i + 1 && j < n && s[j] === ';') return j + 1;
  return 0;
}

// ---------- inline parsing helpers ----------
function isAlnum(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}
function isEmailLocal(c) {
  return isAlnum(c) || c === 46 || c === 33 || c === 35 || c === 36 || c === 37 ||
    c === 38 || c === 39 || c === 42 || c === 43 || c === 47 || c === 61 ||
    c === 63 || c === 94 || c === 95 || c === 96 || c === 123 || c === 124 ||
    c === 125 || c === 126 || c === 45;
}
function isEmailDomain(c) {
  return isAlnum(c) || c === 95 || c === 46 || c === 45;
}
// Pre-pass: find email autolinks (incl. lowercase mailto: prefix).
// Returns flat array [start, end, start, end, ...] sorted by start.
function findEmails(src) {
  const out = [];
  const n = src.length;
  let i = 0;
  while (i < n) {
    const at = src.indexOf('@', i);
    if (at < 0) break;
    let ls = at - 1;
    while (ls >= 0 && isEmailLocal(src.charCodeAt(ls))) ls--;
    ls++;
    if (ls < at) {
      let de = at + 1;
      while (de < n && isEmailDomain(src.charCodeAt(de))) de++;
      let dEnd = de;
      while (dEnd > at + 1 && src.charCodeAt(dEnd - 1) === 46) dEnd--;
      if (dEnd > at + 1) {
        // Email wrapped in underscore emphasis (_an@x.y_, __a_b@c.d__):
        // the leading '_' run was absorbed into the local part and the
        // trailing '_' run into the domain. Strip matching runs when the
        // leading run looks like an opener.
        if (src.charCodeAt(ls) === 95 && src.charCodeAt(dEnd - 1) === 95) {
          let leadRun = 0;
          while (ls + leadRun < at && src.charCodeAt(ls + leadRun) === 95) leadRun++;
          let trailRun = 0;
          while (dEnd - 1 - trailRun > at + 1 && src.charCodeAt(dEnd - 1 - trailRun) === 95) trailRun++;
          const prev = ls === 0 ? 32 : src.charCodeAt(ls - 1);
          if (prev === 32 || prev === 10 || isAsciiPunct(prev)) {
            const strip = Math.min(leadRun, trailRun);
            ls += strip; dEnd -= strip;
          }
        }
        const dom = src.slice(at + 1, dEnd);
        // A trailing '_' may be an emphasis closer (e.g. _foo@bar.baz_): strip
        // it only when a plausible opener '_' exists before the email start.
        if (dom.indexOf('.') >= 0 && dom.indexOf('..') < 0 && dom.charCodeAt(0) !== 46) {
          let end2 = dEnd;
          if (src.charCodeAt(end2 - 1) === 95) {
            let opener = -1;
            for (let k = ls - 1; k >= 0; k--) {
              const c = src.charCodeAt(k);
              if (c === 95) {
                const prev = k === 0 ? 32 : src.charCodeAt(k - 1);
                const next = k + 1 < n ? src.charCodeAt(k + 1) : 32;
                if ((prev === 32 || prev === 10 || isAsciiPunct(prev)) && isAlnum(next)) { opener = k; break; }
              }
            }
            if (opener >= 0) {
              // count the '_' run containing the opener, strip that many
              // trailing '_' (e.g. __a b@c.d__ strips 2)
              let run = 1;
              let k = opener - 1;
              while (k >= 0 && src.charCodeAt(k) === 95) { run++; k--; }
              k = opener + 1;
              while (k < n && src.charCodeAt(k) === 95) { run++; k++; }
              // the run may extend past the opener into the local part; cap
              // by the run that starts at the opener
              let runStart = opener;
              while (runStart > 0 && src.charCodeAt(runStart - 1) === 95) runStart--;
              let runLen = 0;
              while (runStart + runLen < n && src.charCodeAt(runStart + runLen) === 95) runLen++;
              let strip = Math.min(runLen, run);
              while (strip > 0 && end2 > at + 1 && src.charCodeAt(end2 - 1) === 95) { end2--; strip--; }
            }
          }
          if (end2 > at + 1 && isAlnum(src.charCodeAt(end2 - 1))) {
            let start = ls;
            let scheme = '';
            // a preceding scheme: (2-32 chars) directly before the local part
            if (ls > 0 && src.charCodeAt(ls - 1) === 58) {
              let s0 = ls - 2;
              while (s0 >= 0) {
                const c = src.charCodeAt(s0);
                if ((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 43 || c === 46 || c === 45) s0--;
                else break;
              }
              s0++;
              const slen = (ls - 1) - s0;
              if (slen >= 2 && slen <= 32) {
                const fc = src.charCodeAt(s0);
                if ((fc >= 65 && fc <= 90) || (fc >= 97 && fc <= 122)) { start = s0; scheme = src.slice(s0, ls - 1).toLowerCase(); }
              }
            }
            // xmpp: JIDs may carry a single /resource segment
            if (scheme === 'xmpp' && end2 < n && src.charCodeAt(end2) === 47) {
              let r = end2 + 1;
              while (r < n) {
                const c = src.charCodeAt(r);
                if (c === 32 || c === 9 || c === 10 || c === 13 || c === 60 || c === 47 || c === 63 || c === 35) break;
                r++;
              }
              if (r > end2 + 1) {
                let re = r;
                while (re > end2 + 1 && isUrlTrailPunct(src.charCodeAt(re - 1))) re--;
                if (re > end2 + 1) end2 = re;
              }
            }
            out.push(start, end2);
            i = end2;
            continue;
          }
        }
      }
    }
    i = at + 1;
  }
  return out;
}

// Extended autolink (GFM) trailing punctuation to strip.
function isUrlTrailPunct(c) {
  return c === 63 || c === 33 || c === 46 || c === 44 || c === 58 || c === 59 ||
    c === 42 || c === 95 || c === 126 || c === 39 || c === 34 || c === 40;
}
// Match an extended autolink (www. / http:// / https:// / ftp://) starting at i.
// Returns end index (exclusive) or 0. src[i] must be 'w', 'h', or 'f'.
function matchExtUrl(src, i) {
  const n = src.length;
  let start;
  let isWww = false;
  if (src.charCodeAt(i) === 119) { // 'w'
    if (src.slice(i, i + 4) !== 'www.') return 0;
    // preceding-char rule
    if (i > 0) {
      const p = src.charCodeAt(i - 1);
      if (!(p === 95 || p === 47 || p === 40 || p === 126 || p === 42 || p === 62 ||
            p === 32 || p === 9 || p === 10 || p === 13)) return 0;
    }
    start = i;
    isWww = true;
  } else {
    // scheme:// (case-insensitive), only http/https/ftp
    const c1 = src.charCodeAt(i) | 32;
    if (c1 === 104) { // h
      if (src.slice(i + 1, i + 4).toLowerCase() !== 'ttp') return 0;
      let j = i + 4;
      if (src.charCodeAt(j) === 115 || src.charCodeAt(j) === 83) j++; // optional 's'
      if (src.slice(j, j + 3) !== '://') return 0;
      start = i;
    } else if (c1 === 102) { // f
      if (src.slice(i + 1, i + 3).toLowerCase() !== 'tp') return 0;
      if (src.slice(i + 3, i + 6) !== '://') return 0;
      start = i;
    } else return 0;
  }
  // maximal run of non-space, non-'<' chars
  let end = start;
  while (end < n) {
    const c = src.charCodeAt(end);
    if (c === 32 || c === 9 || c === 10 || c === 13 || c === 60) break;
    end++;
  }
  // backpedal trailing punctuation and unbalanced ')' until stable
  // (stripping a ')' can expose a '.' etc. that must also go)
  for (;;) {
    let stripped = false;
    while (end > start && isUrlTrailPunct(src.charCodeAt(end - 1))) { end--; stripped = true; }
    if (end > start && src.charCodeAt(end - 1) === 41) {
      // stack-based: the trailing ')' is stripped only if it does not
      // close a preceding '(' (e.g. /a(b)) -> /a(b), but
      // https://y.io?q=1)](./z.md) keeps its final ')' which closes '(')
      let depth = 0;
      for (let k = start; k < end - 1; k++) {
        const c = src.charCodeAt(k);
        if (c === 40) depth++;
        else if (c === 41 && depth > 0) depth--;
      }
      if (depth === 0) { end--; stripped = true; }
    }
    // a trailing &name; entity (or &name once ';' was stripped) is not
    // part of the URL
    if (end > start) {
      let k = end - 1;
      if (src.charCodeAt(k) === 59) k--;
      while (k >= start && isAlnum(src.charCodeAt(k))) k--;
      if (k >= start && src.charCodeAt(k) === 38 && k + 1 < end) {
        // require the ';' to have been present (or just stripped above)
        end = k; stripped = true;
      }
    }
    if (!stripped) break;
  }
  // truncate at first '(' after the last ')' (only within the URL itself)
  let lastClose = -1;
  for (let k = start; k < end; k++) if (src.charCodeAt(k) === 41) lastClose = k;
  for (let k = Math.max(lastClose + 1, start); k < end; k++) {
    if (src.charCodeAt(k) === 40) { end = k; break; }
  }
  // for www., require at least one more char after 'www.'
  if (isWww && end <= start + 4) return 0;
  if (end <= start) return 0;
  return end;
}

// Find the ']' matching the '[' at src[i]. Handles nested [], escapes, tags.
// Returns index of ']' or -1. A ']' is only the link end if the label
// between '[' and ']' passes labelOk (its backtick runs pair up); a ']'
// that fails labelOk is literal and scanning continues — this keeps a
// backtick run inside the label from pairing with a backtick outside it
// and swallowing the ']' (e.g. "[a ``b`](u) `c`" and "[less `` a ` b ``](u)").
function findLinkTextEnd(src, i) {
  const n = src.length;
  let depth = 0;
  let j = i + 1;
  while (j < n) {
    const c = src.charCodeAt(j);
    if (c === 92) { j += 2; continue; }
    if (c === 91) { depth++; j++; continue; }
    if (c === 93) {
      if (depth === 0) {
        if (labelOk(src.slice(i + 1, j))) return j;
        j++; continue; // ']' is literal: not a valid label end
      }
      depth--; j++; continue;
    }
    if (c === 60) {
      // a <...> tag/autolink hides any ']' inside it (e.g. a quoted
      // attribute value spanning the bracket)
      const tg = tryTag(src, j, false);
      if (tg) { j = tg.end; continue; }
    }
    j++;
  }
  return -1;
}

// Normalize a link label: collapse internal whitespace (incl. newlines) to
// single spaces, trim, lowercase (Unicode-aware via toLowerCase).
function normLabel(s) {
  let out = '';
  let lastWs = true; // leading whitespace trimmed
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 32 || c === 9 || c === 10 || c === 13 || c === 12) {
      if (!lastWs) { out += ' '; lastWs = true; }
    } else {
      out += s[i];
      lastWs = false;
    }
  }
  // trim trailing space
  if (out.length && out.charCodeAt(out.length - 1) === 32) out = out.slice(0, -1);
  // Unicode full case folding: sharp-s folds to "ss" (ẞ -> ß -> ss)
  return out.toLowerCase().replace(/\u00DF/g, 'ss');
}

// Parse the destination + optional title inside parens of an inline link.
// src[i] is just after '('. Returns {dest, title, end} (end = index after
// the closing ')') or null.
function parseDestTitle(src, i) {
  const n = src.length;
  let p = i;
  while (p < n) {
    const c = src.charCodeAt(p);
    if (c === 32 || c === 9 || c === 10 || c === 13) p++;
    else break;
  }
  if (p >= n) return null;
  let dest = '';
  // angle-bracket destination
  if (src.charCodeAt(p) === 60) {
    let q = p + 1;
    let found = false;
    let d = '';
    while (q < n) {
      const c = src.charCodeAt(q);
      if (c === 10 || c === 13) break;
      if (c === 62) { found = true; break; }
      if (c === 92 && q + 1 < n && isAsciiPunct(src.charCodeAt(q + 1))) {
        d += src[q + 1]; q += 2; continue;
      }
      d += src[q]; q++;
    }
    if (!found) return null;
    dest = d;
    p = q + 1;
  } else {
    const b = parseBareDestTitle(src, i);
    if (!b) return null;
    return b;
  }
  // optional title, then ')'
  return parseTitleClose(src, p, dest);
}

// Bare destination: no spaces/control chars, balanced parens, escapes.
function parseBareDestTitle(src, i) {
  const n = src.length;
  let p = i;
  while (p < n) {
    const c = src.charCodeAt(p);
    if (c === 32 || c === 9 || c === 10 || c === 13) p++;
    else break;
  }
  if (p >= n) return null;
  let dest = '';
  let depth = 0;
  let q = p;
  while (q < n) {
    const c = src.charCodeAt(q);
    if (c === 32 || c === 9 || c === 10 || c === 13) break;
    if (c < 32) return null; // control char in destination
    if (c === 40) { depth++; dest += '('; q++; continue; }
    if (c === 41) {
      if (depth === 0) break;
      depth--; dest += ')'; q++; continue;
    }
    if (c === 92 && q + 1 < n) {
      const nc = src.charCodeAt(q + 1);
      if (isAsciiPunct(nc)) { dest += src[q + 1]; q += 2; continue; }
      dest += '\\'; q++; continue;
    }
    dest += src[q]; q++;
  }
  return parseTitleClose(src, q, dest);
}

// After a destination: skip ws, optional title, skip ws, expect ')'.
function parseTitleClose(src, p, dest) {
  const n = src.length;
  while (p < n) {
    const c = src.charCodeAt(p);
    if (c === 32 || c === 9 || c === 10 || c === 13) p++;
    else break;
  }
  if (p >= n) return null;
  if (src.charCodeAt(p) === 41) return { dest, title: null, end: p + 1 };
  // title: "..." or '...' or (...)
  const q0 = src.charCodeAt(p);
  let title = '';
  let q;
  if (q0 === 34 || q0 === 39) {
    q = p + 1;
    let closed = false;
    while (q < n) {
      const c = src.charCodeAt(q);
      if (c === q0) { closed = true; break; }
      if (c === 92 && q + 1 < n && isAsciiPunct(src.charCodeAt(q + 1))) {
        title += src[q + 1]; q += 2; continue;
      }
      title += src[q]; q++;
    }
    if (!closed) return null;
    q++;
  } else if (q0 === 40) {
    q = p + 1;
    let closed = false;
    while (q < n) {
      const c = src.charCodeAt(q);
      if (c === 41) { closed = true; break; }
      if (c === 92 && q + 1 < n && isAsciiPunct(src.charCodeAt(q + 1))) {
        title += src[q + 1]; q += 2; continue;
      }
      title += src[q]; q++;
    }
    if (!closed) return null;
    q++;
  } else return null;
  p = q;
  while (p < n) {
    const c = src.charCodeAt(p);
    if (c === 32 || c === 9 || c === 10 || c === 13) p++;
    else break;
  }
  if (p < n && src.charCodeAt(p) === 41) return { dest, title, end: p + 1 };
  return null;
}

// Mask for emphasis: positions hidden by marked's masked source.
// Returns a Uint8Array (1 = masked) or null when nothing is masked.
// Re-derived from marked's observable behavior (its inline lexer masks
// regions before searching for emphasis closers):
// (1) code spans are found on the raw source by pairing a backtick run
// with the first later run of the same length; their inner backticks are
// neutralized to '+', so a span can start inside a link label and close
// outside it (a "phantom" span); (2) inline links [label](...) whose
// label (after neutralization) holds only plain chars and code spans, and
// resolved reference links, are masked wholesale. A delimiter inside a
// masked region cannot open or close emphasis — e.g. a link label holding
// `` `` `` pairs with a later `` `` `` code span, hiding an _..._ pair
// between them, and a link that only becomes matchable after inner-backtick
// neutralization hides its label's delimiters even when the link itself
// does not form (bad destination).
function computeEmMask(src, defs) {
  const n = src.length;
  if (n === 0) return null;
  let hasBt = false, hasBr = false, hasDelim = false;
  for (let i = 0; i < n; i++) {
    const c = src.charCodeAt(i);
    if (c === 96) hasBt = true;
    else if (c === 91) hasBr = true;
    else if (c === 42 || c === 95 || c === 126) hasDelim = true;
  }
  if (!hasDelim || (!hasBt && !hasBr)) return null;
  const masked = new Uint8Array(n);
  let anyMasked = false;
  // neutralized copy, allocated lazily on the first neutralization
  // (many paragraphs need none, and split+join over a 100KB paragraph
  // is pure overhead then).
  let ch = null;
  const neut = (pos) => { if (!ch) ch = src.split(''); ch[pos] = '+'; };
  // --- Step A: code spans, left-to-right scan of the raw source ---
  // At each position, in order: an escape `\<punct>` is neutralized
  // (both chars become '+'); a backtick run tries to pair with the first
  // later run of the same length. The closing run is a plain backtick
  // run — an escaped backtick CAN close a span (doc-06: the opener after
  // `tool` closes on the `\`` before `default`), because marked tries
  // the code-span alternative before the escape alternative at each
  // position, so an escaped backtick is only neutralized when no earlier
  // opener has already consumed it as a closer. Conversely a `\`` with
  // no earlier opener (doc-02) is neutralized and never opens a span.
  const spans = [];
  let i = 0;
  while (i < n) {
    const c = src.charCodeAt(i);
    if (c === 92 && i + 1 < n && isPunctStr(src[i + 1])) {
      neut(i); neut(i + 1);
      i += 2;
      continue;
    }
    if (c !== 96) { i++; continue; }
    let k = i;
    while (k < n && src.charCodeAt(k) === 96) k++;
    const len = k - i;
    let m = k, found = -1;
    while (m < n) {
      if (src.charCodeAt(m) === 96) {
        let e = m;
        while (e < n && src.charCodeAt(e) === 96) e++;
        if (e - m === len && (e >= n || src.charCodeAt(e) !== 96) && m > k) { found = m; break; }
        m = e;
      } else m++;
    }
    if (found >= 0) {
      spans.push([i, found + len]);
      for (let q = k; q < found; q++) if (src.charCodeAt(q) === 96) neut(q);
      i = found + len;
    } else {
      i = k;
    }
  }
  const neu = ch ? ch.join('') : src;
  // Match a label at neu[pos] === '[' on the neutralized source; returns
  // the index of the closing ']' or -1. Label holds plain chars (not [ ]
  // `) and code spans (run + non-backtick content + same run).
  const matchLabel = (pos) => {
    let p = pos + 1;
    while (p < n) {
      const c = neu.charCodeAt(p);
      if (c === 93) return p;
      if (c === 91 || c === 92) return -1;
      if (c === 96) {
        let k = p;
        while (k < n && neu.charCodeAt(k) === 96) k++;
        const len = k - p;
        let m = k;
        while (m < n && neu.charCodeAt(m) !== 96) m++;
        if (m >= n) return -1;
        let e = m;
        while (e < n && neu.charCodeAt(e) === 96) e++;
        if (e - m !== len || (e < n && neu.charCodeAt(e) === 96)) return -1;
        p = e;
        continue;
      }
      p++;
    }
    return -1;
  };
  // Match the (dest) group at neu[pos] === '('; returns index after ')' or -1.
  // marked's pattern allows nested parens only one level deep.
  const matchParen = (pos) => {
    let p = pos + 1, depth = 1;
    while (p < n) {
      const c = neu.charCodeAt(p);
      if (c === 92) { p += 2; continue; }
      if (c === 40) { depth++; if (depth > 2) return -1; }
      else if (c === 41) { depth--; if (depth === 0) return p + 1; }
      p++;
    }
    return -1;
  };
  // --- Step B: links on the neutralized source ---
  // A '[' inside a code span (step A) is already consumed by that span:
  // skip over spans, exactly as blockSkip's left-to-right alternation does.
  let j = 0, si = 0;
  while (j < n) {
    while (si < spans.length && spans[si][1] <= j) si++;
    if (si < spans.length && spans[si][0] <= j && j < spans[si][1]) { j = spans[si][1]; continue; }
    if (neu.charCodeAt(j) !== 91) { j++; continue; }
    const close = matchLabel(j);
    if (close < 0) { j++; continue; }
    const after = close + 1;
    let end = -1;
    if (after < n && neu.charCodeAt(after) === 40) {
      end = matchParen(after);
    } else if (after < n && neu.charCodeAt(after) === 91) {
      const close2 = matchLabel(after);
      if (close2 >= 0) {
        const ref = close2 === after + 1 ? neu.slice(j + 1, close) : neu.slice(after + 1, close2);
        if (ref.length > 0 && defs && defs[normLabel(ref)]) end = close2 + 1;
      }
    } else {
      const label = neu.slice(j + 1, close);
      if (label.length > 0 && defs && defs[normLabel(label)]) end = after;
    }
    if (end >= 0) {
      for (let q = j; q < end; q++) masked[q] = 1;
      anyMasked = true;
      j = end;
    } else {
      j++;
    }
  }
  // code spans mask their whole range
  for (let s = 0; s < spans.length; s++) {
    for (let q = spans[s][0]; q < spans[s][1]; q++) masked[q] = 1;
    anyMasked = true;
  }
  return anyMasked ? masked : null;
}

// ---------- inline parsing ----------
// Parse inline markdown to HTML. defs: link reference map.
// inLink: inside a link text (no nested links). noHtml: alt-text mode
// (treat '<' as literal text).
// marked quirk: an <a ...> open tag leaves the parser "inside an anchor"
// for the rest of the document, suppressing bare-URL and bare-email
// autolinks (but not [text](url) links or <...> autolinks). It is set by
// a multi-line <a ...> tag (see multiLineAnchorSuppresses) or by a
// single-line <a ...> tag that shares its paragraph with other text;
// a single-line <a ...> tag that IS its whole paragraph does not set it.
// Any </a> met during inline parsing clears it again. A standalone </a>
// line is an HTML block, not inline-parsed, so it does not clear it.
// Reset per document in parse().
let suppressBareAutolink = false;

// Does a multi-line <a ...> open tag suppress later bare autolinks?
// The newline must not be immediately after the tag name, and must not be
// immediately before the closing '>' (allowing whitespace).
function multiLineAnchorSuppresses(t) {
  for (let k = 2; k < t.length; k++) {
    if (t.charCodeAt(k) !== 10) continue;
    if (k === 2) continue; // newline immediately after the tag name
    let j = k + 1;
    while (j < t.length) {
      const c = t.charCodeAt(j);
      if (c === 32 || c === 9 || c === 10 || c === 13 || c === 12) j++;
      else break;
    }
    if (j >= t.length || t.charCodeAt(j) === 62) continue; // followed by '>'
    return true;
  }
  return false;
}

// Is the tag at src[i..end] the whole inline text (only whitespace around it)?
function isOnlyTag(src, i, end) {
  for (let k = 0; k < i; k++) {
    const c = src.charCodeAt(k);
    if (c !== 32 && c !== 9 && c !== 10 && c !== 13 && c !== 12) return false;
  }
  for (let k = end; k < src.length; k++) {
    const c = src.charCodeAt(k);
    if (c !== 32 && c !== 9 && c !== 10 && c !== 13 && c !== 12) return false;
  }
  return true;
}

function parseInline(src, defs, inLink, noHtml) {
  const emails = findEmails(src);
  const emMask = computeEmMask(src, defs); // 1 = hidden by marked's masked source
  const nodes = [];
  const delims = [];
  let textStart = 0;
  let i = 0;
  const n = src.length;
  let emailIdx = 0;
  const flushText = (end) => {
    if (end > textStart) nodes.push({ t: 'text', s: src.slice(textStart, end) });
  };
  while (i < n) {
    // skip emails already passed (e.g. one consumed inside a <...> tag/link)
    while (emailIdx < emails.length && emails[emailIdx] < i) emailIdx += 2;
    if (!inLink && !suppressBareAutolink && emailIdx < emails.length && emails[emailIdx] === i) {
      const eEnd = emails[emailIdx + 1];
      flushText(i);
      const em = src.slice(i, eEnd);
      nodes.push({ t: 'autolink', href: /^[a-zA-Z][a-zA-Z0-9+.-]{1,31}:/.test(em) ? em : 'mailto:' + em, text: em });
      i = eEnd; textStart = i; emailIdx += 2;
      continue;
    }
    const c = src.charCodeAt(i);
    if (c === 92) { // backslash
      const nc = i + 1 < n ? src.charCodeAt(i + 1) : -1;
      if (nc === 10) {
        flushText(i); nodes.push({ t: 'br' }); i += 2;
        while (i < n && (src.charCodeAt(i) === 32 || src.charCodeAt(i) === 9)) i++;
        textStart = i; continue;
      }
      if (nc >= 0 && isAsciiPunct(nc)) {
        flushText(i);
        nodes.push({ t: 'text', s: src[i + 1] });
        i += 2; textStart = i; continue;
      }
      i++; continue;
    }
    if (c === 96) { // code span
      let k = i;
      while (k < n && src.charCodeAt(k) === 96) k++;
      const len = k - i;
      let m = k;
      let found = -1;
      while (m < n) {
        if (src.charCodeAt(m) === 96) {
          let e = m;
          while (e < n && src.charCodeAt(e) === 96) e++;
          if (e - m === len) { found = m; break; }
          m = e;
        } else m++;
      }
      if (found < 0) { i = k; continue; }
      flushText(i);
      let content = src.slice(k, found);
      if (content.indexOf('\n') >= 0) content = content.split('\n').join(' ');
      if (content.length >= 2 && content.charCodeAt(0) === 32 &&
          content.charCodeAt(content.length - 1) === 32) {
        let allSp = true;
        for (let q = 1; q < content.length - 1; q++) {
          if (content.charCodeAt(q) !== 32) { allSp = false; break; }
        }
        if (!allSp) content = content.slice(1, -1);
      }
      nodes.push({ t: 'code', s: content });
      i = found + len; textStart = i; continue;
    }
    if (c === 42 || c === 95 || c === 126) { // * _ ~
      let k = i;
      while (k < n && src.charCodeAt(k) === c) k++;
      const len = k - i;
      if (c === 126 && len >= 3) { i = k; continue; } // 3+ tildes: not a delimiter
      if (emMask && emMask[i]) { i = k; continue; } // hidden in marked's masked source: literal text
      const before = i > 0 ? src[i - 1] : '';
      const after = k < n ? src[k] : '';
      const beforeWs = before === '' || isWSCode(before.charCodeAt(0));
      const afterWs = after === '' || isWSCode(after.charCodeAt(0));
      const beforePunct = before !== '' && isPunctStr(before);
      const afterPunct = after !== '' && isPunctStr(after);
      const leftFlank = !afterWs && (!afterPunct || beforeWs || beforePunct);
      const rightFlank = !beforeWs && (!beforePunct || afterWs || afterPunct);
      let canOpen, canClose;
      if (c === 95) {
        canOpen = leftFlank && (!rightFlank || beforePunct);
        canClose = rightFlank && (!leftFlank || afterPunct);
      } else {
        canOpen = leftFlank;
        canClose = rightFlank;
      }
      flushText(i);
      const prevWs = i === 0 || src.charCodeAt(i - 1) === 32 || src.charCodeAt(i - 1) === 9 || src.charCodeAt(i - 1) === 10 || src.charCodeAt(i - 1) === 13;
      const node = { t: 'delim', ch: c === 42 ? '*' : c === 95 ? '_' : '~', len, canOpen, canClose, usedOpen: 0, usedClose: 0, openTags: null, closeTags: null, prevWs };
      nodes.push(node);
      delims.push(node);
      i = k; textStart = i; continue;
    }
    if (c === 91 || (c === 33 && i + 1 < n && src.charCodeAt(i + 1) === 91)) {
      // '[' or '!['
      const isImg = c === 33;
      const bStart = isImg ? i + 1 : i;
      if (!inLink || isImg) {
        const link = tryLink(src, bStart, defs, inLink, noHtml, isImg);
        if (link) {
          flushText(i);
          nodes.push(link.node);
          i = link.end; textStart = i; continue;
        }
      }
      i++; continue;
    }
    if (c === 60 && !noHtml) { // '<' autolink or inline HTML
      const tag = tryTag(src, i, inLink);
      if (tag) {
        flushText(i);
        nodes.push(tag.node);
        i = tag.end; textStart = i; continue;
      }
      i++; continue;
    }
    if (!inLink && !suppressBareAutolink && (c === 119 || c === 87 || c === 104 || c === 72 || c === 102 || c === 70)) {
      const eEnd = matchExtUrl(src, i);
      if (eEnd > 0) {
        flushText(i);
        const url = src.slice(i, eEnd);
        const href = src.charCodeAt(i) === 119 || src.charCodeAt(i) === 87
          ? 'http://' + url : url;
        nodes.push({ t: 'autolink', href, text: url });
        i = eEnd; textStart = i; continue;
      }
      i++; continue;
    }
    if (c === 10) { // newline: hard break if 2+ trailing spaces
      let sp = 0;
      let j = i - 1;
      while (j >= textStart && src.charCodeAt(j) === 32) { sp++; j--; }
      if (sp >= 2) {
        flushText(i - sp);
        nodes.push({ t: 'br' });
        i++;
        while (i < n && (src.charCodeAt(i) === 32 || src.charCodeAt(i) === 9)) i++;
        textStart = i; continue;
      }
      i++; continue;
    }
    i++;
  }
  flushText(n);
  processDelims(nodes, delims);
  return renderInline(nodes);
}

// Does the link text (s) contain a nested link (a '[' not preceded by '!'
// whose matching ']' is followed by '(' or '[')? Code spans are skipped.
function textHasNestedLink(s, defs) {
  const n = s.length;
  let i = 0;
  while (i < n) {
    const c = s.charCodeAt(i);
    if (c === 96) { // code span: skip to matching run
      let k = i;
      while (k < n && s.charCodeAt(k) === 96) k++;
      const len = k - i;
      let m = k;
      let found = -1;
      while (m < n) {
        if (s.charCodeAt(m) === 96) {
          let e = m;
          while (e < n && s.charCodeAt(e) === 96) e++;
          if (e - m === len) { found = m; break; }
          m = e;
        } else m++;
      }
      if (found < 0) { i = k; continue; }
      i = found + len;
      continue;
    }
    if (c === 92) { i += 2; continue; } // escape
    if (c === 91) { // '['
      if (i > 0 && s.charCodeAt(i - 1) === 33) {
        // image: skip the whole ![...] construct plus its (dest) or
        // [label], so the image's own label bracket is never mistaken
        // for a standalone shortcut link (e.g. ![one][6] inside a link)
        const ic = findLinkTextEnd(s, i);
        if (ic < 0) { i++; continue; }
        let j = ic + 1;
        if (j < n && s.charCodeAt(j) === 40) {
          const dt = parseDestTitle(s, j + 1);
          if (dt) j = dt.end;
        } else if (j < n && s.charCodeAt(j) === 91) {
          const ic2 = findLinkTextEnd(s, j);
          if (ic2 >= 0) j = ic2 + 1;
        }
        i = j;
        continue;
      }
      const close = findLinkTextEnd(s, i);
      if (close >= 0) {
        const inner = s.slice(i + 1, close);
        // an inner link only blocks the outer one if it would form itself
        if (!labelOk(inner)) { i = close + 1; continue; }
        const after = close + 1;
        if (after < n && s.charCodeAt(after) === 40) {
          // inline link: only a nested link if the destination parses;
          // a bad destination falls back to a shortcut reference link
          if (parseDestTitle(s, after + 1)) return true;
          if (inner.length > 0 && defs && defs[normLabel(inner)]) return true;
        } else if (after < n && s.charCodeAt(after) === 91) {
          // reference link: only a nested link if the label resolves
          const close2 = findLinkTextEnd(s, after);
          if (close2 >= 0) {
            const label = close2 === after + 1 ? s.slice(i + 1, close) : s.slice(after + 1, close2);
            if (defs && defs[normLabel(label)]) return true;
          }
        } else {
          // shortcut reference link: [label] with nothing after it —
          // it blocks the outer link when the label resolves
          if (inner.length > 0 && defs && defs[normLabel(inner)]) return true;
        }
        i = close + 1;
        continue;
      }
    }
    i++;
  }
  return false;
}

// Is a candidate link text acceptable as a link label? Mirrors marked's
// observable label rule: backtick runs inside the label must pair up — a
// run pairs with the FIRST later backtick run (any length; the content
// between them may not itself contain a backtick) — or be a run of 2+
// backticks sitting immediately before the closing ']' (an unclosed span
// at the very end of the label). A lone unmatched run anywhere else kills
// the link: "[a ` b](u)" and "[a `` b ` c `` d](u)" stay literal, while
// "[a `x` b `` c ` d](u)" forms (the `` pairs with the later `). Escapes
// are skipped; backticks inside a nested [...] pair are ignored.
function labelOk(s) {
  const n = s.length;
  let i = 0;
  while (i < n) {
    const c = s.charCodeAt(i);
    if (c === 92) { i += 2; continue; } // escape: skip both chars
    if (c === 91) { // '[': skip the whole nested pair, contents included
      let depth = 1, j = i + 1;
      while (j < n && depth > 0) {
        const d = s.charCodeAt(j);
        if (d === 92) { j += 2; continue; }
        if (d === 91) depth++;
        else if (d === 93) depth--;
        j++;
      }
      if (depth > 0) return false; // unbalanced nested bracket
      i = j;
      continue;
    }
    if (c === 96) { // backtick run
      let k = i;
      while (k < n && s.charCodeAt(k) === 96) k++;
      const len = k - i;
      if (len >= 2 && k === n) return true; // 2+ run right before ']'
      // pair with the first later backtick run (any length)
      let m = k;
      let found = false;
      while (m < n) {
        const d = s.charCodeAt(m);
        if (d === 92) { m += 2; continue; }
        if (d === 96) { found = true; break; }
        m++;
      }
      if (!found) return false;
      let e = m;
      while (e < n && s.charCodeAt(e) === 96) e++;
      i = e;
      continue;
    }
    i++;
  }
  return true;
}

// Try to parse a link/image whose '[' is at src[b]. Returns {node, end} or null.
function tryLink(src, b, defs, inLink, noHtml, isImg) {
  const n = src.length;
  const close = findLinkTextEnd(src, b);
  if (close < 0) return null;
  const text = src.slice(b + 1, close);
  if (!labelOk(text)) return null;
  if (!isImg && textHasNestedLink(text, defs)) return null;
  let after = close + 1;
  let dest = null, title = null;
  if (after < n && src.charCodeAt(after) === 40) {
    const dt = parseDestTitle(src, after + 1);
    if (!dt) {
      // inline link invalid: fall back to shortcut reference link
      const ref = defs[normLabel(text)];
      if (!ref || text.length === 0) return null;
      dest = ref.dest; title = ref.title; after = close + 1;
    } else {
      dest = dt.dest; title = dt.title; after = dt.end;
    }
  } else {
    // reference link: [label], [] (collapsed), or shortcut
    let label;
    if (after < n && src.charCodeAt(after) === 91) {
      const close2 = findLinkTextEnd(src, after);
      if (close2 < 0) return null;
      label = close2 === after + 1 ? text : src.slice(after + 1, close2);
      after = close2 + 1;
    } else {
      label = text;
    }
    if (label.length === 0) return null;
    const ref = defs[normLabel(label)];
    if (!ref) return null;
    dest = ref.dest; title = ref.title;
  }
  if (isImg) {
    const altHtml = parseInline(text, defs, inLink, true);
    const alt = stripTags(altHtml);
    return { node: { t: 'img', src: dest, alt, title }, end: after };
  }
  const children = parseInline(text, defs, true, noHtml);
  return { node: { t: 'link', href: dest, title, children }, end: after };
}

// Strip <...> tags from rendered HTML (for image alt text).
// A nested <img> contributes its alt attribute value.
function stripTags(html) {
  let out = '';
  let i = 0;
  const n = html.length;
  while (i < n) {
    const lt = html.indexOf('<', i);
    if (lt < 0) { out += html.slice(i); break; }
    out += html.slice(i, lt);
    const gt = html.indexOf('>', lt + 1);
    if (gt < 0) { out += html.slice(lt); break; }
    if (html.slice(lt, lt + 4).toLowerCase() === '<img') {
      const tag = html.slice(lt, gt + 1);
      const m = tag.match(/alt="([^"]*)"/);
      if (m) out += m[1];
    }
    i = gt + 1;
  }
  return out;
}

// Try to parse an autolink <...> or inline HTML tag at src[i] ('<').
// Returns {node, end} or null.
function tryTag(src, i, inLink) {
  const n = src.length;
  // autolink: <scheme:...> or <email>
  if (i + 1 < n) {
    const c1 = src.charCodeAt(i + 1);
    // scheme: [a-zA-Z][a-zA-Z0-9+.-]{1,31}:
    if ((c1 >= 65 && c1 <= 90) || (c1 >= 97 && c1 <= 122)) {
      let j = i + 1;
      while (j < n) {
        const c = src.charCodeAt(j);
        if ((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) ||
            c === 43 || c === 46 || c === 45) j++;
        else break;
      }
      if (j - (i + 1) >= 2 && j - (i + 1) <= 32 && j < n && src.charCodeAt(j) === 58) {
        // scheme found; scan to '>' with no space/control
        let k = j + 1;
        let ok = false;
        while (k < n) {
          const c = src.charCodeAt(k);
          if (c === 62) { ok = true; break; }
          if (c === 32 || c === 9 || c === 10 || c === 13 || c === 60 || c < 32) break;
          k++;
        }
        if (ok && k > j + 1) {
          const url = src.slice(i + 1, k);
          return { node: { t: 'autolink', href: url, text: url }, end: k + 1 };
        }
      }
    }
    // email autolink: <...@...>
    const gt = src.indexOf('>', i + 1);
    if (gt > i + 1) {
      const inner = src.slice(i + 1, gt);
      if (inner.indexOf('@') > 0 && inner.indexOf(' ') < 0 && inner.indexOf('<') < 0) {
        // validate as email (reuse findEmails on the inner text)
        const em = findEmails(inner);
        if (em.length === 2 && em[0] === 0 && em[1] === inner.length) {
          return { node: { t: 'autolink', href: 'mailto:' + inner, text: inner }, end: gt + 1 };
        }
      }
    }
  }
  // inline HTML
  const html = matchHtmlTag(src, i);
  if (html > 0) {
    const tagText = src.slice(i, html);
    // <a ...> open tag: set the anchor-suppression flag unless it is a
    // single-line tag that is the whole inline text (see above). The tag
    // only counts as an anchor when whitespace follows the name: <a> and
    // <a/> (no space) do not suppress, <a >, <a /> and <a href=...> do.
    // </a> in inline text clears the flag again
    const c1 = tagText.length > 1 ? tagText.charCodeAt(1) : -1;
    if (c1 === 97 || c1 === 65) {
      const c2 = tagText.length > 2 ? tagText.charCodeAt(2) : -1;
      if (c2 === 32 || c2 === 9 || c2 === 10 || c2 === 13 || c2 === 12 || c2 === 62 || c2 === 47) {
        const hasWs = c2 === 32 || c2 === 9 || c2 === 10 || c2 === 13 || c2 === 12;
        if (hasWs && (multiLineAnchorSuppresses(tagText) || !isOnlyTag(src, i, html))) {
          suppressBareAutolink = true;
        }
      }
    } else if (c1 === 47) {
      const c2 = tagText.length > 2 ? tagText.charCodeAt(2) : -1;
      if (c2 === 97 || c2 === 65) {
        const c3 = tagText.length > 3 ? tagText.charCodeAt(3) : -1;
        if (c3 === 32 || c3 === 9 || c3 === 10 || c3 === 13 || c3 === 12 || c3 === 62 || c3 === 47) {
          suppressBareAutolink = false;
        }
      }
    }
    return { node: { t: 'html', s: tagText }, end: html };
  }
  return null;
}

// Match an inline HTML tag (comment, PI, declaration, CDATA, open/close tag)
// at src[i] ('<'). Returns end index or 0.
function matchHtmlTag(src, i) {
  const n = src.length;
  if (i + 1 >= n) return 0;
  const c1 = src.charCodeAt(i + 1);
  if (c1 === 33) {
    if (src.slice(i + 2, i + 4) === '--') {
      // marked quirk: <!--> and <!---> are raw tokens on their own
      if (src.charCodeAt(i + 4) === 62) return i + 5;
      if (src.charCodeAt(i + 4) === 45 && src.charCodeAt(i + 5) === 62) return i + 6;
      const e = src.indexOf('-->', i + 4);
      if (e < 0) return 0;
      return e + 3;
    }
    if (src.slice(i + 2, i + 9) === '[CDATA[') {
      const e = src.indexOf(']]>', i + 9);
      return e < 0 ? 0 : e + 3;
    }
    const c2 = i + 2 < n ? src.charCodeAt(i + 2) : -1;
    if ((c2 >= 65 && c2 <= 90) || (c2 >= 97 && c2 <= 122)) {
      const e = src.indexOf('>', i + 2);
      return e < 0 ? 0 : e + 1;
    }
    return 0;
  }
  if (c1 === 63) {
    const e = src.indexOf('?>', i + 2);
    return e < 0 ? 0 : e + 2;
  }
  let j = i + 1;
  let closing = false;
  if (j < n && src.charCodeAt(j) === 47) { closing = true; j++; }
  if (j >= n) return 0;
  const tc = src.charCodeAt(j);
  if (!((tc >= 65 && tc <= 90) || (tc >= 97 && tc <= 122))) return 0;
  j++;
  while (j < n) {
    const c = src.charCodeAt(j);
    if ((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 45) j++;
    else break;
  }
  for (;;) {
    let sawWs = false;
    while (j < n) {
      const c = src.charCodeAt(j);
      if (c === 32 || c === 9 || c === 10 || c === 13 || c === 12) { j++; sawWs = true; }
      else break;
    }
    if (j >= n) return 0;
    const c = src.charCodeAt(j);
    if (c === 62) return j + 1;
    if (c === 47) {
      if (j + 1 < n && src.charCodeAt(j + 1) === 62) return j + 2;
      return 0;
    }
    // attributes need preceding whitespace; closing tags take none
    if (closing || !sawWs) return 0;
    const ac = src.charCodeAt(j);
    if (!((ac >= 65 && ac <= 90) || (ac >= 97 && ac <= 122) || ac === 95 || ac === 58)) return 0;
    j++;
    while (j < n) {
      const c2 = src.charCodeAt(j);
      if ((c2 >= 48 && c2 <= 57) || (c2 >= 65 && c2 <= 90) || (c2 >= 97 && c2 <= 122) ||
          c2 === 95 || c2 === 58 || c2 === 45 || c2 === 46) j++;
      else break;
    }
    // whitespace before '=' belongs to the attribute separator when no
    // '=' follows (a valueless attribute must not eat the next separator)
    const wsSave = j;
    while (j < n) {
      const c2 = src.charCodeAt(j);
      if (c2 === 32 || c2 === 9 || c2 === 10 || c2 === 13 || c2 === 12) j++;
      else break;
    }
    if (j >= n || src.charCodeAt(j) !== 61) j = wsSave;
    if (j < n && src.charCodeAt(j) === 61) {
      j++;
      while (j < n) {
        const c2 = src.charCodeAt(j);
        if (c2 === 32 || c2 === 9 || c2 === 10 || c2 === 13 || c2 === 12) j++;
        else break;
      }
      if (j >= n) return 0;
      const q = src.charCodeAt(j);
      if (q === 34 || q === 39) {
        const e = src.indexOf(String.fromCharCode(q), j + 1);
        if (e < 0) return 0;
        j = e + 1;
      } else {
        let ok = false;
        while (j < n) {
          const c2 = src.charCodeAt(j);
          if (c2 === 32 || c2 === 9 || c2 === 10 || c2 === 13 || c2 === 12 ||
              c2 === 34 || c2 === 39 || c2 === 61 || c2 === 60 || c2 === 62 || c2 === 96) break;
          j++; ok = true;
        }
        if (!ok) return 0;
      }
    }
  }
}

// Emphasis / strikethrough: cmark delimiter algorithm.
// '~' pairs only with equal-length runs (probed); '*'/'_' use rule of 3.
function processDelims(nodes, delims) {
  const openers = [];
  for (let di = 0; di < delims.length; di++) {
    const closer = delims[di];
    if (closer.canClose) {
      // A closer may match several openers in turn (e.g. *a *b**).
      for (;;) {
        const closerRem = closer.len - closer.usedOpen - closer.usedClose;
        if (closerRem <= 0) break;
        // find nearest unmatched opener with same char
        let oi = openers.length - 1;
        let matched = false;
        while (oi >= 0) {
          const opener = openers[oi];
          if (opener.ch !== closer.ch) { oi--; continue; }
          const openerRem = opener.len - opener.usedOpen - opener.usedClose;
          if (openerRem <= 0) { openers.splice(oi, 1); oi--; continue; }
          if (closer.ch === '~') {
            if (openerRem !== closerRem) { oi--; continue; }
            const use = openerRem;
            opener.usedOpen += use;
            closer.usedClose += use;
            insertEm(nodes, opener, closer, 'del');
            // openers after the matched one lie inside the new emphasis
            // and can no longer pair with a closer outside it
            openers.length = oi + 1;
            if (opener.len - opener.usedOpen - opener.usedClose <= 0) openers.splice(oi, 1);
            matched = true;
            break;
          }
          // rule of 3: blocked if EITHER delimiter can both open and close
          // and the sum of remaining lengths is a multiple of 3 (unless both
          // are multiples of 3).
          const eitherBoth = (opener.canOpen && opener.canClose) || (closer.canOpen && closer.canClose);
          if (eitherBoth && (openerRem + closerRem) % 3 === 0 &&
              !(openerRem % 3 === 0 && closerRem % 3 === 0)) {
            oi--; continue;
          }
          // A closer that would only partly consume an opener defers when a
          // later closer could consume the opener fully (e.g. **a *b*c* d**).
          if (openerRem > closerRem) {
            let laterFull = false;
            for (let dj = di + 1; dj < delims.length; dj++) {
              const later = delims[dj];
              if (later.ch !== closer.ch) continue;
              if (!later.canClose) continue;
              const laterRem = later.len - later.usedOpen - later.usedClose;
              if (laterRem >= openerRem) { laterFull = true; break; }
            }
            if (laterFull) { oi--; continue; }
          }
          const use = openerRem >= 2 && closerRem >= 2 ? 2 : 1;
          // A strong whose opener can only open (preceded by whitespace)
          // and whose closer is followed by non-whitespace text blocks an
          // outer single-delimiter match (e.g. *a **b**c* stays literal,
          // while *foo**bar**baz*, *a **b** c* and *a **b*** form emphasis).
          if (use === 1) {
            const ci = nodes.indexOf(closer);
            if (ci > 1) {
              const prev = nodes[ci - 1];
              const prev2 = nodes[ci - 2];
              if (prev && prev.t === 'text' && prev.s.length && prev.s.charCodeAt(0) !== 32 && prev.s.charCodeAt(0) !== 9 && prev.s.charCodeAt(0) !== 10 &&
                  prev2 && prev2.t === 'delim' && prev2.closeTags && prev2.closeTags.indexOf('strong') >= 0) {
                // The blocking strong is the one prev2 closes: use its
                // matching opener (linked in insertEm), and only when it
                // uses the same delimiter character as this closer. An
                // unrelated earlier strong (e.g. __pull__ on a previous
                // line) must not block a _..._ match.
                // A blocked opener is dead: remove it from the pool, so a
                // later closer cannot pick it up as a single-delimiter
                // match either (e.g. **removes example *input **parse**
                // parse* release** must end as one strong, and
                // *a **b**c* d* must leave both * literal).
                const openerNode = prev2._partner;
                if (openerNode && openerNode.ch === closer.ch && openerNode.prevWs) { openers.splice(oi, 1); oi--; continue; }
              }
            }
          }
          opener.usedOpen += use;
          closer.usedClose += use;
          insertEm(nodes, opener, closer, use === 2 ? 'strong' : 'em');
          // openers after the matched one lie inside the new emphasis
          // and can no longer pair with a closer outside it
          openers.length = oi + 1;
          if (opener.len - opener.usedOpen - opener.usedClose <= 0) openers.splice(oi, 1);
          matched = true;
          break;
        }
        if (!matched) break;
      }
    }
    const rem = closer.len - closer.usedOpen - closer.usedClose;
    if (closer.canOpen && rem > 0 && openers.indexOf(closer) < 0) openers.push(closer);
  }
}

// Insert <tag> after the opener node and </tag> before the closer node.
function insertEm(nodes, opener, closer, tag) {
  const oi = nodes.indexOf(opener);
  const ci = nodes.indexOf(closer);
  if (oi < 0 || ci < 0) return;
  // A strong whose span holds an emphasis closed by a delimiter that can
  // also open (e.g. **a *b*c***, where the * after b is followed by a
  // word char) splits a trailing closer run differently: up to `use`
  // literal delimiters stay INSIDE the strong, before its close tag
  // (marked renders **a *b*c*** as <strong>a <em>b</em>c*</strong>).
  // Remember that on the closer so the renderer can place the remainder.
  if (tag === 'strong') {
    for (let q = oi + 1; q < ci; q++) {
      const nd = nodes[q];
      if (nd.t === 'delim' && nd.canOpen && nd.canClose && nd.usedClose > 0) { closer._splitStrong = true; break; }
    }
  }
  // remember the pairing: the strong-blocking heuristic above must test
  // the opener of the strong immediately before a closer, not just any
  // earlier strong with the same delimiter character.
  opener._partner = closer;
  closer._partner = opener;
  // opener tags: outermost first -> unshift (later pairs are outer)
  if (!opener.openTags) opener.openTags = [];
  opener.openTags.unshift(tag);
  if (!closer.closeTags) closer.closeTags = [];
  closer.closeTags.push(tag);
}

// Render a node list to HTML.
function renderInline(nodes) {
  let out = '';
  for (let k = 0; k < nodes.length; k++) {
    const nd = nodes[k];
    switch (nd.t) {
      case 'text': out += esc(nd.s); break;
      case 'br': out += '<br>'; break;
      case 'code': out += '<code>' + escRaw(nd.s) + '</code>'; break;
      case 'html': out += nd.s; break;
      case 'autolink':
        out += '<a href="' + encodeHref(nd.href, true) + '">' + escRaw(nd.text) + '</a>';
        break;
      case 'link': {
        out += '<a href="' + encodeHref(nd.href) + '"';
        if (nd.title !== null && nd.title !== undefined) out += ' title="' + esc(nd.title) + '"';
        out += '>' + nd.children + '</a>';
        break;
      }
      case 'img': {
        out += '<img src="' + encodeHref(nd.src) + '" alt="' + nd.alt + '"';
        if (nd.title !== null && nd.title !== undefined) out += ' title="' + esc(nd.title) + '"';
        out += '>';
        break;
      }
      case 'delim': {
        const rem = nd.len - nd.usedOpen - nd.usedClose;
        // A split strong (see insertEm): up to 2 literal delimiters of a
        // partially-used closer run stay inside the strong, before its
        // close tag; the rest render after it as usual.
        let before = 0;
        if (rem > 0 && nd._splitStrong && nd.closeTags && nd.closeTags.indexOf('strong') >= 0) {
          before = Math.min(rem, 2);
          out += esc(nd.ch.repeat(before));
        }
        if (nd.closeTags) {
          for (let q = 0; q < nd.closeTags.length; q++) out += '</' + nd.closeTags[q] + '>';
        }
        if (rem - before > 0) out += esc(nd.ch.repeat(rem - before));
        if (nd.openTags) {
          for (let q = 0; q < nd.openTags.length; q++) out += '<' + nd.openTags[q] + '>';
        }
        break;
      }
    }
  }
  return out;
}

// ---------- block parsing ----------

// Strip up to n columns of leading whitespace (partial tab -> spaces).
// Returns {text, col}; never fails (strips what is available).
function stripColsUpTo(s, col0, n) {
  let col = col0;
  let i = 0;
  const target = col0 + n;
  while (i < s.length && col < target) {
    const c = s.charCodeAt(i);
    if (c === 32) { col++; i++; }
    else if (c === 9) {
      const next = (Math.floor(col / 4) + 1) * 4;
      if (next <= target) { col = next; i++; }
      else return { text: s.slice(i + 1), col: target }; // straddled tab: remove entirely
    } else break;
  }
  return { text: s.slice(i), col };
}

// Strip n columns of leading whitespace from s (absolute column col0).
// Partial tab -> spaces. Returns {text, col} or null if not enough whitespace.
function stripCols(s, col0, n, expandBoundary) {
  let col = col0;
  let i = 0;
  const target = col0 + n;
  while (i < s.length && col < target) {
    const c = s.charCodeAt(i);
    if (c === 32) { col++; i++; }
    else if (c === 9) {
      const next = (Math.floor(col / 4) + 1) * 4;
      if (next <= target) { col = next; i++; }
      else return { text: ' '.repeat(next - target) + s.slice(i + 1), col: target };
    } else return null;
  }
  if (col < target) return null;
  // stripping ended exactly at a tab: expand it to spaces (its width)
  // (only for container indentation, not for indented-code stripping)
  if (expandBoundary && i < s.length && s.charCodeAt(i) === 9 && n > 0) {
    const next = (Math.floor(col / 4) + 1) * 4;
    return { text: ' '.repeat(next - col) + s.slice(i + 1), col: next };
  }
  return { text: s.slice(i), col };
}
// Columns of leading whitespace in s starting at absolute column col0.
function leadingCols(s, col0) {
  let col = col0;
  let i = 0;
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === 32) { col++; i++; }
    else if (c === 9) { col = (Math.floor(col / 4) + 1) * 4; i++; }
    else break;
  }
  return { cols: col - col0, index: i };
}
// Expand leading tabs to spaces (content starts at absolute column col0).
function expandLeadingTabs(s, col0) {
  let col = col0;
  let i = 0;
  let out = '';
  let hasTab = false;
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === 32) { out += ' '; col++; i++; }
    else if (c === 9) {
      hasTab = true;
      const next = (Math.floor(col / 4) + 1) * 4;
      out += ' '.repeat(next - col);
      col = next; i++;
    } else break;
  }
  if (!hasTab) return s;
  return out + s.slice(i);
}
function isBlankStr(s) {
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c !== 32 && c !== 9 && c !== 12 && c !== 13) return false;
  }
  return true;
}
// Count leading spaces (no tabs) up to 4; returns {spaces, index}.
function leadingSpaces(s) {
  let i = 0;
  while (i < s.length && i < 4 && s.charCodeAt(i) === 32) i++;
  return i;
}

const BLOCK6_TAGS = new Set(('address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem nav noframes ol optgroup option p param section source summary table tbody td tfoot th thead title tr track ul').split(' '));

// Try to parse a link reference definition starting at s (already stripped of
// up to 3 spaces indent). Returns {dest, title, end} (end = index in s after
// the definition, may span lines via next) or null. next = function to get
// the following line's text (for multi-line defs) or null.
// This handles single-line defs; multi-line (dest/title on next line) is
// handled by the caller with the returned partial state.
// Parse a link reference definition. content = current line's stripped
// content (starts with '['). peek(n) = stripped content of the n-th
// following line, or null. Returns {label, dest, title, linesConsumed} or null.

// Parse a link title that may span lines. getLine(k) returns line k.
// Starts at (startLine, startOff) which must be a quote char (" ' or ().
// Returns {title, endLine, endOff} (endOff = just after closing quote) or null.
function parseTitleMulti(getLine, startLine, startOff) {
  const first = getLine(startLine);
  if (first === null) return null;
  const q0 = first.charCodeAt(startOff);
  const closer = q0 === 40 ? 41 : q0;
  let title = '';
  let line = startLine;
  let p = startOff + 1;
  for (;;) {
    const cur = getLine(line);
    if (cur === null) return null;
    while (p < cur.length) {
      const c = cur.charCodeAt(p);
      if (c === closer) return { title, endLine: line, endOff: p + 1 };
      if (c === 92 && p + 1 < cur.length && isAsciiPunct(cur.charCodeAt(p + 1))) { title += cur[p + 1]; p += 2; continue; }
      title += cur[p]; p++;
    }
    // end of line without closing quote: newline joins the title
    title += '\n';
    line++;
    p = 0;
  }
}

function parseDefAt(content, peek) {
  // skip up to 3 leading spaces (a def may be indented 0-3)
  let s0 = 0;
  while (s0 < content.length && s0 < 3 && content.charCodeAt(s0) === 32) s0++;
  if (s0 > 0) content = content.slice(s0);
  if (content.charCodeAt(0) !== 91) return null;
  // line cache: line 0 = content, line k = peek(k)
  const lines = [content];
  const getLine = (k) => {
    while (lines.length <= k) {
      const nx = peek(lines.length);
      if (nx === null) return null;
      lines.push(nx);
    }
    return lines[k];
  };
  // Find the label end (may span lines).
  let label = null;
  let labelEndLine = 0, labelEndOff = 0; // position just after ']'
  {
    const close = findLinkTextEnd(content, 0);
    if (close >= 0) {
      label = content.slice(1, close);
      labelEndLine = 0; labelEndOff = close + 1;
    } else {
      let combined = content;
      let found = -1;
      for (let k = 1; k <= 4; k++) {
        const nx = getLine(k);
        if (nx === null) break;
        combined += '\n' + nx;
        const c2 = findLinkTextEnd(combined, 0);
        if (c2 >= 0) { found = c2; break; }
      }
      if (found < 0) return null;
      label = combined.slice(1, found);
      const parts = combined.split('\n');
      let acc = 0;
      for (let li = 0; li < parts.length; li++) {
        if (found < acc + parts[li].length) {
          labelEndLine = li;
          labelEndOff = found - acc + 1;
          break;
        }
        acc += parts[li].length + 1;
      }
    }
  }
  if (label === null || label.length === 0) return null;
  // a label may not contain an unescaped '[' and may not be whitespace-only
  {
    let bad = false;
    for (let k = 0; k < label.length; k++) {
      if (label.charCodeAt(k) === 91 && (k === 0 || label.charCodeAt(k - 1) !== 92)) { bad = true; break; }
    }
    if (bad || normLabel(label) === '') return null;
  }
  let curLine = labelEndLine;
  let cur = lines[curLine];
  let curOff = labelEndOff;
  const advanceLine = () => {
    const nx = getLine(curLine + 1);
    if (nx === null) return false;
    curLine++;
    cur = nx; curOff = 0;
    return true;
  };
  // skip spaces to ':'
  while (curOff < cur.length && (cur.charCodeAt(curOff) === 32 || cur.charCodeAt(curOff) === 9)) curOff++;
  if (curOff >= cur.length || cur.charCodeAt(curOff) !== 58) return null;
  curOff++;
  // skip whitespace (possibly across lines) to destination
  for (;;) {
    while (curOff < cur.length && (cur.charCodeAt(curOff) === 32 || cur.charCodeAt(curOff) === 9)) curOff++;
    if (curOff < cur.length) break;
    if (!advanceLine()) return null;
  }
  let dest;
  if (cur.charCodeAt(curOff) === 60) {
    let q = curOff + 1;
    let d = '';
    let found = false;
    while (q < cur.length) {
      const c = cur.charCodeAt(q);
      if (c === 62) { found = true; break; }
      if (c === 92 && q + 1 < cur.length && isAsciiPunct(cur.charCodeAt(q + 1))) { d += cur[q + 1]; q += 2; continue; }
      d += cur[q]; q++;
    }
    if (!found) return null;
    dest = d;
    curOff = q + 1;
  } else {
    let q = curOff;
    let d = '';
    let depth = 0;
    while (q < cur.length) {
      const c = cur.charCodeAt(q);
      if (c === 32 || c === 9) break;
      if (c < 32) return null;
      if (c === 40) { depth++; d += '('; q++; continue; }
      if (c === 41) {
        if (depth === 0) break;
        depth--; d += ')'; q++; continue;
      }
      if (c === 92 && q + 1 < cur.length) {
        const nc = cur.charCodeAt(q + 1);
        if (isAsciiPunct(nc)) { d += cur[q + 1]; q += 2; continue; }
        d += '\\'; q++; continue;
      }
      d += cur[q]; q++;
    }
    if (q === curOff) return null;
    dest = d;
    curOff = q;
  }
  // optional title (may span lines). A title on the same line must be
  // preceded by whitespace.
  let title = null;
  const afterDest = curOff;
  while (curOff < cur.length && (cur.charCodeAt(curOff) === 32 || cur.charCodeAt(curOff) === 9)) curOff++;
  if (curOff >= cur.length) {
    // title may be on the next line, but only if it consumes the whole line
    const nx = getLine(curLine + 1);
    if (nx !== null) {
      let q = 0;
      while (q < nx.length && (nx.charCodeAt(q) === 32 || nx.charCodeAt(q) === 9)) q++;
      if (q < nx.length) {
        const q0 = nx.charCodeAt(q);
        if (q0 === 34 || q0 === 39 || q0 === 40) {
          const t = parseTitleMulti(getLine, curLine + 1, q);
          if (t !== null) {
            const endLine = getLine(t.endLine);
            let e = t.endOff;
            while (e < endLine.length && (endLine.charCodeAt(e) === 32 || endLine.charCodeAt(e) === 9)) e++;
            if (e >= endLine.length) {
              title = t.title;
              curLine = t.endLine;
            }
          }
        }
      }
    }
  } else {
    const q0 = cur.charCodeAt(curOff);
    if (q0 === 34 || q0 === 39 || q0 === 40) {
      if (curOff === afterDest) return null; // no whitespace before title
      const t = parseTitleMulti(getLine, curLine, curOff);
      if (t === null) return null;
      title = t.title;
      curLine = t.endLine;
      cur = getLine(curLine);
      curOff = t.endOff;
      while (curOff < cur.length && (cur.charCodeAt(curOff) === 32 || cur.charCodeAt(curOff) === 9)) curOff++;
      if (curOff < cur.length) return null;
    } else {
      return null;
    }
  }
  return { label, dest, title, linesConsumed: curLine };
}

function parseTitleOnly(cur, p) {
  const q0 = cur.charCodeAt(p);
  let title = '';
  let q;
  if (q0 === 34 || q0 === 39) {
    q = p + 1;
    while (q < cur.length) {
      const c = cur.charCodeAt(q);
      if (c === q0) return { title, end: q + 1 };
      if (c === 92 && q + 1 < cur.length && isAsciiPunct(cur.charCodeAt(q + 1))) { title += cur[q + 1]; q += 2; continue; }
      title += cur[q]; q++;
    }
    return null;
  }
  q = p + 1;
  while (q < cur.length) {
    const c = cur.charCodeAt(q);
    if (c === 41) return { title, end: q + 1 };
    if (c === 92 && q + 1 < cur.length && isAsciiPunct(cur.charCodeAt(q + 1))) { title += cur[q + 1]; q += 2; continue; }
    title += cur[q]; q++;
  }
  return null;
}

// Match a blockquote '>' marker. Returns {content, col} or null.
function matchQuoteMarker(s, col0) {
  let i = 0;
  let col = col0;
  while (i < s.length && i < 3 && s.charCodeAt(i) === 32) { i++; col++; }
  if (i >= s.length || s.charCodeAt(i) !== 62) return null;
  i++; col++;
  if (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === 32) { i++; col++; }
    else if (c === 9) {
      const next = (Math.floor(col / 4) + 1) * 4;
      if (next - col === 1) { i++; col = next; }
      else return { content: ' '.repeat(next - col - 1) + s.slice(i + 1), col: col + 1 };
    }
  }
  return { content: s.slice(i), col };
}
function isAncestorBlock(b, leaf) {
  let p = leaf.parent;
  while (p) {
    if (p === b) return true;
    p = p.parent;
  }
  return false;
}
// Does this line start a block that would interrupt a paragraph / close a
// list item or blockquote (so it is NOT a lazy continuation)?

// A list marker that may interrupt a paragraph: any bullet, or an ordered
// list whose start number is 1.
function listInterrupts(content, col) {
  const m = matchListMarker(content, col);
  if (!m) return false;
  if (!m.ordered) return true;
  return m.start === 1;
}
function startsInterruptTop(content, col) {
  if (matchFenceOpen(content)) return true;
  if (matchAtx(content)) return true;
  if (isThematicBreak(content)) return true;
  if (matchQuoteMarker(content, col)) return true;
  if (matchListMarker(content, col)) return true;
  const h = matchHtmlBlockStart(content);
  if (h && h.type !== 7) return true;
  return false;
}
// Match open containers against a line. Pure.
// Returns {content, col, depth, lazy, strippedAny}.
// depth = index of innermost matched container in stack (stack truncated to depth+1).
function matchContainers(line, stack, openLeaf) {
  let content = line;
  let col = 0;
  let depth = 0;
  let strippedAny = false;
  let strippedQuote = false;
  let lazy = false;
  // Column base for tab expansion: when the content sits inside a container
  // nested in another container (a quote in a list item, a quote in a
  // quote), marked expands a leading tab relative to the OUTERMOST
  // container's content start, not the absolute column
  // (`- a\n  > \tfoo` -> 2 spaces, not 4; `> > \tfoo` -> 2, not 4).
  // A single top-level quote keeps the absolute column
  // (`> \tfoo` -> 2, `   > \tfoo` -> 3). tabColBase is the absolute col
  // just after the first container was stripped; nested is set when a
  // second container is stripped.
  let tabColBase = -1;
  let nested = false;
  // index of the innermost open list item, if any
  let deepestItem = -1;
  for (let k = stack.length - 1; k >= 1; k--) {
    if (stack[k].t === 'item') { deepestItem = k; break; }
  }
  for (let s = 1; s < stack.length; s++) {
    const b = stack[s];
    if (b.t === 'quote') {
      // A nested quote's marker (and a tab right after '>') is expanded in
      // the PARENT container's frame: the content starts at column 0 there,
      // so pass 0 and convert the returned col back to absolute. A
      // top-level quote keeps the absolute column.
      const nestedQ = tabColBase >= 0;
      const absBefore = col;
      const m = matchQuoteMarker(content, nestedQ ? 0 : col);
      if (!m) {
        if (openLeaf && openLeaf.t === 'para' && isAncestorBlock(b, openLeaf) && !isBlankStr(content) && !startsInterruptTop(content, col)) { lazy = true; }
        break;
      }
      content = m.content; col = nestedQ ? absBefore + m.col : m.col; strippedAny = true; strippedQuote = true;
      if (tabColBase < 0) tabColBase = col; else nested = true;
      depth = s;
    } else if (b.t === 'list') {
      // list itself consumes nothing; its item decides
      continue;
    } else if (b.t === 'item') {
      // an empty item followed by a blank line is closed: indented content
      // after it belongs outside the list
      if (b.children.length === 0 && b.lastBlank && !isBlankStr(content)) break;
      if (isBlankStr(content)) {
        // blank line: inside the item; strip its indent if possible.
        // The indent is relative to where this line's container content
        // starts (a quote may eat 0 or 1 space after '>' on different
        // lines), so strip indentRel columns, not indent-col.
        const strip = b.indentRel;
        if (strip > 0) {
          const r = stripCols(content, col, strip);
          if (r) { content = r.text; col = r.col; }
          else { content = ''; col = col + b.indentRel; }
        }
        if (tabColBase < 0) tabColBase = col; else nested = true;
        depth = s;
        continue;
      }
      const lc = leadingCols(content, col);
      const C = lc.cols;
      const R = b.indentRel; // item content indent, relative to the
      // container-content start of the item's own line (see above)
      if (C >= R) {
        let strip = R;
        // Deep-indented paragraph continuation: a line indented 4+ past
        // the item's content indent is still paragraph text (it cannot
        // start a code block or a new list while the paragraph is open),
        // with 4 extra columns stripped. Only the INNERMOST item may
        // take this strip: an outer item must not eat the indentation a
        // deeper item needs to match the line (cf. cm-294, where the
        // line belongs to the deepest nested list, not to the outer para).
        if (s === deepestItem && C - R >= 4 && openLeaf && openLeaf.t === 'para' && isAncestorBlock(b, openLeaf)) strip = R + 4;
        const r = stripCols(content, col, strip, true);
        if (!r) break;
        content = r.text; col = r.col; strippedAny = true;
        if (tabColBase < 0) tabColBase = col; else nested = true;
        depth = s;
      } else {
        // A fence inside a list item is a lazy continuation only once it
        // has received real (non-blank) content and no blank line has
        // intervened: marked closes an empty fence on the first outside
        // line (`- a\n  ```\nfoo` -> empty fence + paragraph) but keeps
        // lazy lines once content exists (`- a\n  ```\n  foo\nbar`).
        if (openLeaf && (openLeaf.t === 'para' || (openLeaf.t === 'fence' && openLeaf._lazyOk)) && isAncestorBlock(b, openLeaf) && !isBlankStr(content) && !startsInterruptTop(content, col)) { lazy = true; }
        break;
      }
    }
  }
  const tabCol = nested && tabColBase >= 0 ? col - tabColBase : col;
  return { content, col, depth, lazy, strippedAny, strippedQuote, tabCol };
}


// Expand leading tabs of a fence-content line as if the stripped content
// starts at column 2 (marked's behaviour inside a container: a tab at
// stripped position p becomes next4(p+2)-(p+2) spaces). At top level
// (col 0) tabs are preserved, so callers only use this when col > 0.
function expandFenceTabs(c) {
  let i = 0;
  let col = 2;
  let out = '';
  while (i < c.length) {
    const ch = c.charCodeAt(i);
    if (ch === 32) { out += ' '; col++; i++; }
    else if (ch === 9) {
      const next = (Math.floor(col / 4) + 1) * 4;
      out += ' '.repeat(next - col);
      col = next; i++;
    } else break;
  }
  if (i === 0) return c;
  return out + c.slice(i);
}

// ---------- main parse ----------
export function parse(markdown) {
  suppressBareAutolink = false;
  const refs = {};
  const src = markdown.replace(/\r\n?/g, '\n');
  const lines = src.split('\n');
  if (lines.length && lines[lines.length - 1] === '') lines.pop();
  const root = { t: 'doc', children: [], parent: null, lastBlank: false };
  const stack = [root];
  let openLeaf = null;

  const tipBlock = () => openLeaf || stack[stack.length - 1];
  const resetBlank = (b) => { let p = b; while (p) { p.lastBlank = false; p = p.parent; } };
  const setBlank = () => {
    let p = tipBlock();
    while (p) { p.lastBlank = true; p = p.parent; }
    // also mark the last child chain: a blank line after a fence/para/etc
    // inside an item must make the list loose
    let q = tipBlock();
    while (q && q.children && q.children.length > 0) {
      q = q.children[q.children.length - 1];
      q.lastBlank = true;
    }
  };
  const addBlock = (b) => { const parent = stack[stack.length - 1]; b.parent = parent; parent.children.push(b); return b; };
  const closeLeaf = () => {
    if (!openLeaf) return;
    const b = openLeaf; openLeaf = null;
    if (b.t === 'icode') {
      b.text = b.text.replace(/^\n+/, '').replace(/\n+$/, '\n');
      if (b.text === '') b.text = '';
    }
  };
  const applyDepth = (depth) => {
    if (openLeaf && openLeaf.parent) {
      const idx = stack.indexOf(openLeaf.parent);
      if (idx < 0 || idx > depth) closeLeaf();
    }
    while (stack.length > depth + 1) stack.pop();
  };
  const peekContent = (li, offset) => {
    const idx = li + offset;
    if (idx >= lines.length) return null;
    const raw = lines[idx];
    if (isBlankStr(raw)) return null;
    const m = matchContainers(raw, stack, null);
    if (m.depth < stack.length - 1) return null;
    return m.content;
  };
  const startsInterrupt = (content, col) => {
    if (matchFenceOpen(content)) return true;
    if (matchAtx(content)) return true;
    if (isThematicBreak(content)) return true;
    if (matchQuoteMarker(content, col)) return true;
    const lm = matchListMarker(content, col);
    if (lm) {
      // an empty list item (marker alone) cannot interrupt a paragraph
      if (lm.blankItem) return false;
      if (!lm.ordered || lm.start === 1) return true;
      // an ordered list with start != 1 may interrupt a paragraph only
      // when the paragraph is inside a list item (nested list)
      if (openLeaf && openLeaf.t === 'para' && openLeaf.parent && openLeaf.parent.t === 'item') return true;
      return false;
    }
    const h = matchHtmlBlockStart(content);
    if (h && h.type !== 7) return true;
    return false;
  };

  // Process content as a new block. Opens a leaf (sets openLeaf) or a
  // container (quote/list, recursing on the remainder). Returns extra lines
  // consumed (multi-line defs) or 0.
  const processNewBlock = (content, col, strippedAny, li) => {
    const fence = matchFenceOpen(content);
    if (fence) {
      const b = { t: 'fence', info: fence.info, text: '', fenceChar: fence.ch, fenceLen: fence.len, fenceIndent: fence.indent, _lazyOk: false, parent: null, children: [], lastBlank: false };
      addBlock(b); openLeaf = b; resetBlank(b);
      return 0;
    }
    const atx = matchAtx(content);
    if (atx) {
      const b = { t: 'atx', level: atx.level, text: atx.text, parent: null, children: [], lastBlank: false };
      addBlock(b); resetBlank(b);
      return 0;
    }
    if (isThematicBreak(content)) {
      const b = { t: 'hr', parent: null, children: [], lastBlank: false };
      addBlock(b); resetBlank(b);
      return 0;
    }
    const qm = matchQuoteMarker(content, col);
    if (qm) {
      const b = { t: 'quote', parent: null, children: [], lastBlank: false };
      addBlock(b); stack.push(b); resetBlank(b);
      const rest = qm.content;
      if (rest !== '' && !isBlankStr(rest)) return processNewBlock(rest, qm.col, true, li);
      return 0;
    }
    const lst = matchListMarker(content, col);
    if (lst) {
      const parent = stack[stack.length - 1];
      let list = null;
      const last = parent.children[parent.children.length - 1];
      if (last && last.t === 'list' && last.ordered === lst.ordered &&
          (lst.ordered ? last.delim === lst.delim : last.bullet === lst.bullet)) {
        list = last;
      } else {
        list = { t: 'list', ordered: lst.ordered, delim: lst.delim, bullet: lst.bullet, start: lst.start, parent: null, children: [], lastBlank: false };
        addBlock(list);
      }
      const item = { t: 'item', indent: lst.contentIndent, indentRel: lst.contentIndent - col, markerEnd: lst.markerEnd, markerStart: lst.markerStart, ordered: lst.ordered, parent: list, children: [], lastBlank: false };
      list.children.push(item);
      stack.push(list, item);
      resetBlank(item);
      if (!lst.blankItem && lst.rest !== '' && !isBlankStr(lst.rest)) {
        return processNewBlock(lst.rest, lst.restCol, true, li);
      }
      return 0;
    }
    const html = matchHtmlBlockStart(content);
    if (html) {
      const b = { t: 'html', text: content + '\n', htmlType: html.type, endTag: html.endTag, parent: null, children: [], lastBlank: false };
      addBlock(b);
      // types 1-5 may end on the same line they start (e.g. <!-- ... -->)
      if (html.type >= 1 && html.type <= 5 && htmlBlockEnds(b, content)) {
        openLeaf = null;
      } else {
        openLeaf = b;
      }
      resetBlank(b);
      return 0;
    }
    {
      const lc = leadingCols(content, col);
      if (lc.cols >= 4) {
        const r = stripCols(content, col, 4);
        let c = r ? r.text : content;
        if (strippedAny) c = expandLeadingTabs(c, col + 4);
        const b = { t: 'icode', text: c + '\n', parent: null, children: [], lastBlank: false };
        addBlock(b); openLeaf = b; resetBlank(b);
        return 0;
      }
    }
    {
      const def = parseDefAt(content, (n) => peekContent(li, n));
      if (def) {
        const key = normLabel(def.label);
        if (!(key in refs)) refs[key] = { dest: def.dest, title: def.title };
        return def.linesConsumed;
      }
    }
    {
      let c = content;
      if (strippedAny) c = expandLeadingTabs(c, col);
      const b = { t: 'para', text: c, parent: null, children: [], lastBlank: false };
      addBlock(b); openLeaf = b; resetBlank(b);
      return 0;
    }
  };

  for (let li = 0; li < lines.length; li++) {
    const rawLine = lines[li];
    if (isBlankStr(rawLine) && !(openLeaf && openLeaf.t === 'table' && rawLine.indexOf('\t') >= 0)) {
      setBlank();
      let joinedLeaf = false;
      if (openLeaf) {
        if (openLeaf.t === 'para') closeLeaf();
        else if (openLeaf.t === 'table') closeLeaf();
        else if (openLeaf.t === 'html' && (openLeaf.htmlType === 6 || openLeaf.htmlType === 7)) {
          if (openLeaf.text.endsWith('\n')) openLeaf.text = openLeaf.text.slice(0, -1);
          closeLeaf();
        }
        else if (openLeaf.t === 'fence' || openLeaf.t === 'icode' || openLeaf.t === 'html') {
          // blank line joins the leaf only if it is inside the leaf's containers
          const m = matchContainers(rawLine, stack, openLeaf);
          const parentIdx = stack.indexOf(openLeaf.parent);
          if (parentIdx <= m.depth) {
            joinedLeaf = true;
            if (openLeaf.t === 'fence') {
              let c = m.content;
              if (openLeaf.fenceIndent > 0 && openLeaf.fenceChar === '`') {
                const r = stripColsUpTo(c, m.col, openLeaf.fenceIndent);
                c = r.text;
              }
              openLeaf.text += c + '\n';
              openLeaf._lazyOk = false;
            } else if (openLeaf.t === 'icode') {
              const r = stripCols(m.content, m.col, 4);
              openLeaf.text += (r ? r.text : '') + '\n';
            } else {
              openLeaf.text += m.content + '\n';
            }
            // a blank line inside a fence/code/HTML block is content, not a
            // separator: it must not make an enclosing list loose
            resetBlank(openLeaf);
          } else {
            closeLeaf();
          }
        }
      }
      if (!joinedLeaf) {
        // A truly blank line after a list inside a blockquote closes the
        // quote: marked splits `> - a\n\n> b` into two blockquotes, while
        // `> foo\n\n> bar` stays one (handled by the loop below, which
        // only pops quotes at the stack tip). The list/item sit above the
        // quote on the stack, so find the innermost quote reachable
        // through list/item blocks only; if its last child is a list,
        // pop down to and including it.
        for (let s = stack.length - 1; s >= 1; s--) {
          const b = stack[s];
          if (b.t === 'quote') {
            const kids = b.children;
            if (kids.length > 0 && kids[kids.length - 1].t === 'list') {
              while (stack.length - 1 >= s) { if (openLeaf) closeLeaf(); stack.pop(); }
            }
            break;
          }
          if (b.t !== 'list' && b.t !== 'item') break;
        }
        // a truly blank line closes blockquotes (but not lists/list items)
        while (stack.length > 1 && stack[stack.length - 1].t === 'quote') {
          if (openLeaf) closeLeaf();
          stack.pop();
        }
        // an HTML block followed by a truly empty blank line loses its
        // trailing newline; a whitespace-only line (tab/spaces) keeps it
        const tip = stack[stack.length - 1];
        if (rawLine.length === 0 && tip && tip.children && tip.children.length > 0) {
          const last = tip.children[tip.children.length - 1];
          if (last.t === 'html' && last !== openLeaf && last.text.endsWith('\n')) {
            last.text = last.text.slice(0, -1);
          }
        }
      }
      continue;
    }
    const m = matchContainers(rawLine, stack, openLeaf);
    const content = m.content;
    const col = m.col;
    const tabCol = m.tabCol;
    const strippedAny = m.strippedAny;
    if (m.lazy) {
      // lazy continuation: do NOT touch the stack; the paragraph / fence continues
      if (openLeaf && openLeaf.t === 'fence') {
        let c = content;
        if (col > 0) c = expandFenceTabs(c);
        if (openLeaf.fenceIndent > 0 && openLeaf.fenceChar === '`') {
          const r = stripColsUpTo(c, col, openLeaf.fenceIndent);
          c = r.text;
        }
        openLeaf.text += c + '\n';
        openLeaf._lazyOk = true;
        resetBlank(openLeaf);
        continue;
      }
      if (openLeaf && openLeaf.t === 'para') {
        let c = content;
        let inQuote = false;
        let p = openLeaf.parent;
        while (p) { if (p.t === 'quote') { inQuote = true; break; } p = p.parent; }
        if (inQuote) {
          const lc = leadingCols(c, col);
          if (lc.cols >= 4) {
            const r = stripCols(c, col, 4);
            if (r) c = r.text;
          }
          // marked quirk: a lazy setext '=' line inside a quote is kept
          // in the paragraph with 4 spaces prepended
          if (matchSetext(c) === 1) c = '    ' + c.replace(/^ +/, '');
        }
        // lazy continuation inside a list item: if the line is indented
        // at least to the marker end, strip leading whitespace up to the
        // item's content indent; otherwise keep the leading spaces
        {
          let q = openLeaf.parent;
          while (q) {
            if (q.t === 'item') {
              const lc = leadingCols(c, col);
              if ((q.markerEnd - col) >= 4 && lc.cols >= (q.markerEnd - col)) {
                const r = stripColsUpTo(c, col, q.indent - col);
                c = r.text;
              }
              break;
            }
            q = q.parent;
          }
        }
        // a leading tab in a lazy continuation expands on the ABSOLUTE
        // column: the line failed to match the containers, so it is not
        // inside them (unlike a normal continuation, which uses tabCol)
        c = expandLeadingTabs(c, col);
        openLeaf.text += '\n' + c;
        resetBlank(openLeaf);
      }
      continue;
    }
    applyDepth(m.depth);
    if (isBlankStr(content)) {
      // e.g. ">  " : whitespace-only content inside matched containers.
      // Non-empty whitespace is paragraph content (a space), not a blank
      // line; only truly empty content closes the paragraph.
      if (content.length > 0 && strippedAny && openLeaf && openLeaf.t === 'para') {
        openLeaf.text += '\n' + content;
        resetBlank(openLeaf);
        continue;
      }
      // an empty quote line (e.g. ">") is not a blank line when the quote
      // is nested inside a list item (it does not separate blocks there).
      // When the quote contains the list, the blank line DOES separate
      // items and must set the flag.
      let skipBlank = false;
      if (m.strippedQuote) {
        for (let s = 1; s <= m.depth && s < stack.length; s++) {
          const b = stack[s];
          if (b.t === 'quote') {
            let p = b.parent;
            while (p) { if (p.t === 'item') { skipBlank = true; break; } p = p.parent; }
            break;
          }
        }
      }
      if (!skipBlank) setBlank();
      if (openLeaf) {
        if (openLeaf.t === 'table' && content.indexOf('\t') >= 0) {
          addTableRow(openLeaf, content);
          resetBlank(openLeaf);
          continue;
        }
        if (openLeaf.t === 'para' || openLeaf.t === 'table') closeLeaf();
        else if (openLeaf.t === 'html' && (openLeaf.htmlType === 6 || openLeaf.htmlType === 7)) {
          if (openLeaf.text.endsWith('\n')) openLeaf.text = openLeaf.text.slice(0, -1);
          closeLeaf();
        }
        else if (openLeaf.t === 'fence') {
          let c = content;
          if (openLeaf.fenceIndent > 0 && openLeaf.fenceChar === '`') {
            const r = stripColsUpTo(c, col, openLeaf.fenceIndent);
            c = r.text;
          }
          openLeaf.text += c + '\n';
          openLeaf._lazyOk = false;
        }
        else if (openLeaf.t === 'icode') {
          const r = stripCols(content, col, 4);
          openLeaf.text += (r ? r.text : '') + '\n';
        }
        else if (openLeaf.t === 'html') {
          openLeaf.text += content + '\n';
        }
      }
      continue;
    }
    if (openLeaf) {
      if (openLeaf.t === 'fence') {
        if (matchFenceClose(content, openLeaf)) {
          // the last content line, if blank, is not content
          if (openLeaf.text === '\n' || openLeaf.text.endsWith('\n\n')) openLeaf.text = openLeaf.text.slice(0, -1);
          closeLeaf(); continue;
        }
        let c = content;
        if (col > 0) c = expandFenceTabs(c);
        if (openLeaf.fenceIndent > 0 && openLeaf.fenceChar === '`') {
          const r = stripColsUpTo(c, col, openLeaf.fenceIndent);
          c = r.text;
        }
        openLeaf.text += c + '\n';
        openLeaf._lazyOk = true;
        resetBlank(openLeaf);
        continue;
      }
      if (openLeaf.t === 'html') {
        if (openLeaf.htmlType >= 1 && openLeaf.htmlType <= 5 && htmlBlockEnds(openLeaf, content)) {
          openLeaf.text += content + '\n';
          closeLeaf();
          continue;
        } else {
          openLeaf.text += content + '\n';
          resetBlank(openLeaf);
          continue;
        }
      }
      if (openLeaf && openLeaf.t === 'icode') {
        const lc = leadingCols(content, col);
        if (lc.cols >= 4) {
          const r = stripCols(content, col, 4);
          let c = r ? r.text : content;
          if (strippedAny) c = expandLeadingTabs(c, col + 4);
          openLeaf.text += c + '\n';
          resetBlank(openLeaf);
          continue;
        }
        closeLeaf();
      }
      if (openLeaf && openLeaf.t === 'table') {
        const endsTable = startsInterrupt(content, col);
        const lc = leadingCols(content, col);
        if (!endsTable && lc.cols < 4) {
          addTableRow(openLeaf, content);
          resetBlank(openLeaf);
          continue;
        }
        closeLeaf();
      }
      if (openLeaf && openLeaf.t === 'para') {
        const st = matchSetext(content);
        if (st) {
          let text = openLeaf.text;
          let te = text.length;
          while (te > 0 && (text.charCodeAt(te - 1) === 32 || text.charCodeAt(te - 1) === 9)) te--;
          text = text.slice(0, te);
          let ts = 0;
          while (ts < text.length && (text.charCodeAt(ts) === 32 || text.charCodeAt(ts) === 9)) ts++;
          text = text.slice(ts);
          const parent = openLeaf.parent;
          const idx = parent.children.indexOf(openLeaf);
          const h = { t: 'atx', level: st, text, parent, children: [], lastBlank: false };
          parent.children[idx] = h;
          openLeaf = null;
          resetBlank(h);
          continue;
        }
        const aligns = isTableDelim(content);
        if (aligns) {
          const res = tryMakeTable(openLeaf, aligns);
          if (res) {
            const parent = openLeaf.parent;
            const idx = parent.children.indexOf(openLeaf);
            if (res.beforeText !== null) {
              const p2 = { t: 'para', text: res.beforeText, parent, children: [], lastBlank: false };
              parent.children[idx] = p2;
              parent.children.splice(idx + 1, 0, res.table);
              res.table.parent = parent;
            } else {
              parent.children[idx] = res.table;
              res.table.parent = parent;
            }
            openLeaf = res.table;
            resetBlank(res.table);
            continue;
          }
        }
        if (!startsInterrupt(content, col)) {
          let c = content;
          if (strippedAny) c = expandLeadingTabs(c, tabCol);
          openLeaf.text += '\n' + c;
          resetBlank(openLeaf);
          continue;
        }
        closeLeaf();
      }
    }
    const consumed = processNewBlock(content, col, strippedAny, li);
    if (consumed) li += consumed;
  }
  closeLeaf();
  // an HTML block holding the input's last line has no trailing newline
  // when the input itself does not end with one
  if (src.length && src.charCodeAt(src.length - 1) !== 10) {
    let node = root;
    while (node.children && node.children.length) node = node.children[node.children.length - 1];
    if (node.t === 'html' && node.text.endsWith('\n')) node.text = node.text.slice(0, -1);
  }
  return renderBlocks(root.children, refs);
}

// Match an ATX heading. Returns {level, text} or null.
function matchAtx(s) {
  let i = 0;
  while (i < s.length && i < 3 && s.charCodeAt(i) === 32) i++;
  if (i >= s.length || s.charCodeAt(i) !== 35) return null;
  let level = 0;
  while (i + level < s.length && s.charCodeAt(i + level) === 35 && level < 6) level++;
  if (level === 0 || level > 6) return null;
  // after the run of #'s, need space/tab/EOL, or it's not a heading
  const after = i + level;
  if (after < s.length) {
    const c = s.charCodeAt(after);
    if (c !== 32 && c !== 9) return null;
  }
  let text = s.slice(after);
  // strip trailing spaces/tabs
  let end = text.length;
  while (end > 0 && (text.charCodeAt(end - 1) === 32 || text.charCodeAt(end - 1) === 9)) end--;
  text = text.slice(0, end);
  // closing sequence: a run of #'s at the end preceded by a space/tab
  // (the space after the opening #'s counts)
  if (text.length > 0 && text.charCodeAt(text.length - 1) === 35) {
    let k = text.length - 1;
    while (k >= 0 && text.charCodeAt(k) === 35) k--;
    if (k >= 0 && (text.charCodeAt(k) === 32 || text.charCodeAt(k) === 9)) {
      text = text.slice(0, k + 1);
      let e2 = text.length;
      while (e2 > 0 && (text.charCodeAt(e2 - 1) === 32 || text.charCodeAt(e2 - 1) === 9)) e2--;
      text = text.slice(0, e2);
    }
  }
  // strip leading spaces/tabs
  let j = 0;
  while (j < text.length && (text.charCodeAt(j) === 32 || text.charCodeAt(j) === 9)) j++;
  text = text.slice(j);
  return { level, text };
}
// Match a setext underline. Returns 1 or 2 or 0.
function matchSetext(s) {
  let i = 0;
  while (i < s.length && i < 3 && s.charCodeAt(i) === 32) i++;
  if (i >= s.length) return 0;
  const ch = s.charCodeAt(i);
  if (ch !== 61 && ch !== 45) return 0; // '=' or '-'
  let j = i;
  while (j < s.length && s.charCodeAt(j) === ch) j++;
  while (j < s.length && (s.charCodeAt(j) === 32 || s.charCodeAt(j) === 9)) j++;
  if (j < s.length) return 0;
  return ch === 61 ? 1 : 2;
}
// Thematic break: 3+ of same marker (*, -, _) with only spaces/tabs between.
function isThematicBreak(s) {
  let i = 0;
  while (i < s.length && i < 3 && s.charCodeAt(i) === 32) i++;
  if (i >= s.length) return false;
  const ch = s.charCodeAt(i);
  if (ch !== 42 && ch !== 45 && ch !== 95) return false;
  let count = 0;
  let j = i;
  while (j < s.length) {
    const c = s.charCodeAt(j);
    if (c === ch) { count++; j++; }
    else if (c === 32 || c === 9) j++;
    else return false;
  }
  return count >= 3;
}
// Fenced code open. Returns {ch, len, info, indent} or null.
function matchFenceOpen(s) {
  let i = 0;
  let indent = 0;
  while (i < s.length && i < 3 && s.charCodeAt(i) === 32) { i++; indent++; }
  if (i >= s.length) return null;
  const ch = s.charCodeAt(i);
  if (ch !== 96 && ch !== 126) return null;
  let len = 0;
  while (i + len < s.length && s.charCodeAt(i + len) === ch) len++;
  if (len < 3) return null;
  const infoStart = i + len;
  const info = s.slice(infoStart);
  if (ch === 96 && info.indexOf('`') >= 0) return null;
  // info = first word only, trimmed; backslash escapes resolved
  let infoText = '';
  let k = 0;
  while (k < info.length && (info.charCodeAt(k) === 32 || info.charCodeAt(k) === 9)) k++;
  while (k < info.length && info.charCodeAt(k) !== 32 && info.charCodeAt(k) !== 9) {
    if (info.charCodeAt(k) === 92 && k + 1 < info.length && isAsciiPunct(info.charCodeAt(k + 1))) {
      infoText += info[k + 1]; k += 2; continue;
    }
    infoText += info[k]; k++;
  }
  return { ch: ch === 96 ? '`' : '~', len, info: infoText, indent };
}
// Fenced code close: same char, length >= opening, only spaces after.
function matchFenceClose(s, fence) {
  let i = 0;
  while (i < s.length && i < 3 && s.charCodeAt(i) === 32) i++;
  if (i >= s.length) return false;
  const ch = fence.fenceChar === '`' ? 96 : 126;
  if (s.charCodeAt(i) !== ch) return false;
  let len = 0;
  while (i + len < s.length && s.charCodeAt(i + len) === ch) len++;
  if (len < fence.fenceLen) return false;
  let j = i + len;
  while (j < s.length && (s.charCodeAt(j) === 32 || s.charCodeAt(j) === 9)) j++;
  return j >= s.length;
}
// List marker. s starts at absolute column col0.
// Returns {ordered, delim, bullet, start, contentIndent, rest, restCol, markerEnd} or null.
// contentIndent/restCol are ABSOLUTE columns.
function matchListMarker(s, col0) {
  let i = 0;
  while (i < s.length && i < 3 && s.charCodeAt(i) === 32) i++;
  if (i >= s.length) return null;
  const c = s.charCodeAt(i);
  let ordered = false, delim = '', bullet = '', start = 1, markerEnd = 0;
  if (c === 45 || c === 43 || c === 42) {
    bullet = String.fromCharCode(c);
    markerEnd = i + 1;
  } else if (c >= 48 && c <= 57) {
    let j = i;
    while (j < s.length && s.charCodeAt(j) >= 48 && s.charCodeAt(j) <= 57) j++;
    if (j - i > 9) return null;
    if (j >= s.length) return null;
    const d = s.charCodeAt(j);
    if (d !== 46 && d !== 41) return null;
    ordered = true;
    delim = String.fromCharCode(d);
    start = parseInt(s.slice(i, j), 10);
    markerEnd = j + 1;
  } else return null;
  // whitespace after marker
  let j = markerEnd;
  let col = col0 + markerEnd;
  let wsEnd = j;
  while (wsEnd < s.length) {
    const cc = s.charCodeAt(wsEnd);
    if (cc === 32) { col++; wsEnd++; }
    else if (cc === 9) {
      col = (Math.floor(col / 4) + 1) * 4;
      wsEnd++;
    } else break;
  }
  const totalWs = col - (col0 + markerEnd);
  if (wsEnd >= s.length) {
    // blank item: content indent = marker width + 1
    return { ordered, delim, bullet, start, contentIndent: col0 + markerEnd + 1, rest: '', restCol: col, markerEnd, markerStart: col0 + i, blankItem: true };
  }
  if (totalWs === 0) return null; // no space after marker
  let contentIndent;
  let rest, restCol;
  if (totalWs >= 5) {
    contentIndent = col0 + markerEnd + 1;
    const afterMarker = s.slice(markerEnd);
    const r = stripCols(afterMarker, col0 + markerEnd, 1);
    rest = r ? r.text : afterMarker.slice(1);
    restCol = col0 + markerEnd + 1;
  } else {
    contentIndent = col;
    rest = s.slice(wsEnd);
    restCol = col;
  }
  return { ordered, delim, bullet, start, contentIndent, rest, restCol, markerEnd, markerStart: col0 + i, blankItem: false };
}

// HTML block start. Returns {type, endTag} or null. type 1-7.
function matchHtmlBlockStart(s) {
  let i = 0;
  while (i < s.length && i < 3 && s.charCodeAt(i) === 32) i++;
  if (i >= s.length || s.charCodeAt(i) !== 60) return null; // '<'
  const rest = s.slice(i);
  // type 1: script, pre, textarea, style — OPENING tag only (CommonMark:
  // the start condition is "<pre" etc., never a closing tag; "</pre>" alone
  // is a type 7 tag and cannot interrupt a paragraph, cf. spec ex. 148)
  const m1 = rest.match(/^<(script|pre|textarea|style)(?=[\s>\/]|$)/i);
  if (m1) return { type: 1, endTag: m1[1].toLowerCase() };
  // type 2: comment
  if (rest.startsWith('<!--')) return { type: 2, endTag: null };
  // type 3: processing instruction
  if (rest.startsWith('<?')) return { type: 3, endTag: null };
  // type 4: declaration
  if (/^<![A-Za-z]/.test(rest)) return { type: 4, endTag: null };
  // type 5: CDATA
  if (rest.startsWith('<![CDATA[')) return { type: 5, endTag: null };
  // type 6: block-level tag (tag may span lines; only the start must match)
  const m6 = rest.match(/^<\/?([A-Za-z][A-Za-z0-9-]*)(\s|\/?>|\/?$)/);
  if (m6 && BLOCK6_TAGS.has(m6[1].toLowerCase())) {
    return { type: 6, endTag: null };
  }
  // type 7: any other open/close tag alone on the line
  // (validated with the same tag matcher as inline HTML)
  const tagEnd = matchHtmlTag(rest, 0);
  if (tagEnd > 0) {
    let j = tagEnd;
    while (j < rest.length && (rest.charCodeAt(j) === 32 || rest.charCodeAt(j) === 9)) j++;
    if (j >= rest.length) return { type: 7, endTag: null };
    return null;
  }
  return null;
}
// Does this line end an open HTML block? (checked before adding the line)
function htmlBlockEnds(b, line) {
  if (b.htmlType === 1) {
    const re = new RegExp('</' + b.endTag + '>', 'i');
    return re.test(line);
  }
  if (b.htmlType === 2) return line.indexOf('-->') >= 0;
  if (b.htmlType === 3) return line.indexOf('?>') >= 0;
  if (b.htmlType === 4) return line.indexOf('>') >= 0;
  if (b.htmlType === 5) return line.indexOf(']]>') >= 0;
  if (b.htmlType === 6) return false; // ends at blank line (handled by caller)
  return false;
}

// ---------- tables ----------
// Split a table line into cells (naive on |, respecting \| escapes).
// Returns array of cell strings (trimmed) or null if the line has no pipes
// in a way that makes it a table row.
function splitTableRow(s) {
  let i = 0;
  while (i < s.length && i < 3 && s.charCodeAt(i) === 32) i++;
  let line = s.slice(i);
  // trim trailing spaces
  let end = line.length;
  while (end > 0 && (line.charCodeAt(end - 1) === 32 || line.charCodeAt(end - 1) === 9)) end--;
  line = line.slice(0, end);
  if (line.length === 0) return null;
  let leadingPipe = false, trailingPipe = false;
  if (line.charCodeAt(0) === 124) { leadingPipe = true; line = line.slice(1); }
  if (line.length && line.charCodeAt(line.length - 1) === 124) {
    // check it's not escaped
    if (line.length < 2 || line.charCodeAt(line.length - 2) !== 92) { trailingPipe = true; line = line.slice(0, -1); }
  }
  const cells = [];
  let cur = '';
  for (let k = 0; k < line.length; k++) {
    const c = line.charCodeAt(k);
    if (c === 92 && k + 1 < line.length && line.charCodeAt(k + 1) === 124) { cur += '|'; k++; continue; }
    if (c === 124) { cells.push(cur); cur = ''; continue; }
    cur += line[k];
  }
  cells.push(cur);
  // trim each cell (spaces only)
  for (let k = 0; k < cells.length; k++) {
    let a = cells[k];
    let st = 0, en = a.length;
    while (st < en && a.charCodeAt(st) === 32) st++;
    while (en > st && a.charCodeAt(en - 1) === 32) en--;
    cells[k] = a.slice(st, en);
  }
  return cells;
}
// Is this line a table delimiter row? Returns aligns array or null.
function isTableDelim(s) {
  // a delimiter line indented 4+ spaces is not a table delimiter
  let ind = 0;
  while (ind < s.length && s.charCodeAt(ind) === 32) ind++;
  if (ind >= 4) return null;
  const cells = splitTableRow(s);
  if (!cells) return null;
  const aligns = [];
  for (const cell of cells) {
    const t = cell;
    let a = 0, b = t.length;
    while (a < b && t.charCodeAt(a) === 32) a++;
    while (b > a && t.charCodeAt(b - 1) === 32) b--;
    const c = t.slice(a, b);
    if (!/^:?-+:?$/.test(c)) return null;
    const left = c.charCodeAt(0) === 58;
    const right = c.charCodeAt(c.length - 1) === 58;
    aligns.push(left && right ? 'center' : right ? 'right' : left ? 'left' : null);
  }
  return aligns;
}
// Is this line a plausible table body row (has a pipe or is a single cell)?
// For continuation, any non-blank line that isn't another block start is a row.
// We use: the line (after stripping) contains '|' or is a continuation.
// Here we accept any line that splitTableRow can parse.
function isTableRow(s) {
  return splitTableRow(s) !== null;
}
// (tryMakeTable is defined below with aligns)

// Convert an open paragraph into a table. aligns = delimiter aligns.
// Returns {table, beforeText} or null. beforeText = paragraph text to keep
// before the table (null if the whole paragraph is the header).
function tryMakeTable(para, aligns) {
  const text = para.text;
  const lastNl = text.lastIndexOf('\n');
  const headerLine = lastNl < 0 ? text : text.slice(lastNl + 1);
  const headCells = splitTableRow(headerLine);
  if (!headCells) return null;
  if (headCells.length !== aligns.length) return null;
  const table = { t: 'table', head: headCells, aligns, rows: [], parent: null, children: [], lastBlank: false };
  const beforeText = lastNl < 0 ? null : text.slice(0, lastNl);
  return { table, beforeText };
}
function addTableRow(table, content) {
  let cells = splitTableRow(content);
  if (!cells) cells = [''];
  const n = table.head.length;
  while (cells.length < n) cells.push('');
  if (cells.length > n) cells.length = n;
  table.rows.push(cells);
}

// ---------- rendering ----------
function renderTable(b, refs) {
  let out = '<table>\n<thead>\n<tr>\n';
  for (let k = 0; k < b.head.length; k++) {
    const al = b.aligns[k];
    out += '<th' + (al ? ' align="' + al + '"' : '') + '>' + parseInline(b.head[k], refs, false, false) + '</th>\n';
  }
  out += '</tr>\n</thead>\n';
  if (b.rows.length) {
    out += '<tbody>';
    for (const row of b.rows) {
      out += '<tr>\n';
      for (let k = 0; k < row.length; k++) {
        const al = b.aligns[k];
        out += '<td' + (al ? ' align="' + al + '"' : '') + '>' + parseInline(row[k], refs, false, false) + '</td>\n';
      }
      out += '</tr>\n';
    }
    out += '</tbody>';
  }
  out += '</table>\n';
  return out;
}
function listIsLoose(list) {
  for (let i = 0; i < list.children.length; i++) {
    const item = list.children[i];
    if (i < list.children.length - 1 && item.lastBlank) return true;
    for (let j = 0; j < item.children.length - 1; j++) {
      if (item.children[j].lastBlank) return true;
    }
  }
  return false;
}
// Task-list marker at the start of a list item's first paragraph.
// Returns {checkbox, rest} or null.
function stripTaskMarker(text) {
  if (text.length < 3) return null;
  if (text.charCodeAt(0) !== 91) return null; // [
  if (text.charCodeAt(2) !== 93) return null; // ]
  const c = text.charCodeAt(1);
  let checked;
  if (c === 32) checked = false;
  else if (c === 120 || c === 88) checked = true; // x or X
  else return null;
  if (text.length === 3) return { checkbox: checked ? '<input checked="" disabled="" type="checkbox"> ' : '<input disabled="" type="checkbox"> ', rest: '' };
  if (text.charCodeAt(3) !== 32 && text.charCodeAt(3) !== 9) return null;
  return { checkbox: checked ? '<input checked="" disabled="" type="checkbox"> ' : '<input disabled="" type="checkbox"> ', rest: text.slice(4) };
}
// Render a loose list item's children, handling a task checkbox on the
// first paragraph.
function renderItemLoose(item, refs) {
  let out = '';
  const chs = item.children;
  for (let i = 0; i < chs.length; i++) {
    const b = chs[i];
    if (i === 0 && b.t === 'para') {
      const tm = stripTaskMarker(b.text);
      if (tm) {
        out += '<p>' + tm.checkbox + parseInline(tm.rest, refs, false, false) + '</p>\n';
        continue;
      }
    }
    out += renderBlocks([b], refs);
  }
  const last = chs[chs.length - 1];
  if (last && last.t === 'html' && out.endsWith('\n')) out = out.slice(0, -1);
  return out;
}

function renderBlocks(blocks, refs) {
  let out = '';
  for (const b of blocks) {
    switch (b.t) {
      case 'para':
        out += '<p>' + parseInline(b.text, refs, false, false) + '</p>\n';
        break;
      case 'atx':
        out += '<h' + b.level + '>' + parseInline(b.text, refs, false, false) + '</h' + b.level + '>\n';
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'fence': {
        out += '<pre><code';
        if (b.info) out += ' class="language-' + esc(b.info) + '"';
        out += '>' + escRaw(b.text) + '</code></pre>\n';
        break;
      }
      case 'icode':
        out += '<pre><code>' + escRaw(b.text) + '</code></pre>\n';
        break;
      case 'html':
        out += b.text;
        break;
      case 'quote':
        out += '<blockquote>\n' + renderBlocks(b.children, refs) + '</blockquote>\n';
        break;
      case 'list': {
        const tag = b.ordered ? 'ol' : 'ul';
        out += '<' + tag;
        if (b.ordered && b.start !== 1) out += ' start="' + b.start + '"';
        out += '>\n';
        const loose = listIsLoose(b);
        for (const item of b.children) {
          out += '<li>';
          if (loose) {
            out += renderItemLoose(item, refs);
          } else {
            // tight: render children without <p> wrappers for paragraphs
            out += renderTightItem(item, refs);
          }
          out += '</li>\n';
        }
        out += '</' + tag + '>\n';
        break;
      }
      case 'table':
        out += renderTable(b, refs);
        break;
    }
  }
  return out;
}
// Render a tight list item's children: paragraphs render as inline content
// (no <p>), other blocks render normally.
function renderTightItem(item, refs) {
  let out = '';
  const chs = item.children;
  for (let i = 0; i < chs.length; i++) {
    const b = chs[i];
    if (b.t === 'para') {
      if (i === 0) {
        const tm = stripTaskMarker(b.text);
        if (tm) {
          out += tm.checkbox + parseInline(tm.rest, refs, false, false);
          continue;
        }
      }
      out += parseInline(b.text, refs, false, false);
      // no trailing newline after a paragraph in a tight item
    } else {
      out += renderBlocks([b], refs);
    }
  }
  const last = chs[chs.length - 1];
  if (last && last.t === 'html' && out.endsWith('\n')) out = out.slice(0, -1);
  return out;
}
