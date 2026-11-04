"""A bounded, unescaped subset of Lean 4.19 declaration identifiers.

Based on Init/Meta.lean isIdFirst/isIdRest. Module names deliberately use a
separate ASCII grammar because they also select files. No normalization,
quoted identifiers, punctuation operators, or guessed aliases are accepted.
"""
import re
import unicodedata

MAX_NAME_LENGTH = 200


def _letter_like(code):
    # The pinned Lean ranges contain a few punctuation/symbol characters too.
    # Retain letters only; this application does not need the full lexer syntax.
    return (unicodedata.category(chr(code)).startswith('L') and (
        0x3B1 <= code <= 0x3C9 and code != 0x3BB or
        0x391 <= code <= 0x3A9 and code not in (0x3A0, 0x3A3) or
        0x3CA <= code <= 0x3FB or 0x1F00 <= code <= 0x1FFE or
        0x2100 <= code <= 0x214F or 0x1D49C <= code <= 0x1D59F))


_LETTERS = ''.join(chr(code) for lo, hi in [(0x391, 0x3FB), (0x1F00, 0x1FFE),
                    (0x2100, 0x214F), (0x1D49C, 0x1D59F)]
                   for code in range(lo, hi + 1) if _letter_like(code))
_FIRST = 'A-Za-z_' + re.escape(_LETTERS)
_REST = _FIRST + "0-9'\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
_SEGMENT = '[' + _FIRST + '][' + _REST + ']*'
_QUALIFIED = _SEGMENT + r'(?:\.' + _SEGMENT + ')*'

DECLARATION_NAME = re.compile(r'(?=.{1,' + str(MAX_NAME_LENGTH) + r'}\Z)' + _QUALIFIED)
MODULE_NAME = re.compile(r'(?=.{1,200}\Z)[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')
# Boundaries deliberately recognize MORE than this application's accepted
# subset: Lean also treats !, ?, and every isLetterLike codepoint as name rest.
# Reject unsupported whole tokens instead of extracting/replacing their prefix.
_BOUNDARY = (r"\w.'!?\u0391-\u03fb\u1f00-\u1ffe\u2100-\u214f"
             r"\U0001d49c-\U0001d59f\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c")
_TOKEN = re.compile('(?<![' + _BOUNDARY + '])' + _QUALIFIED + '(?![' + _BOUNDARY + '])')


def identifier_tokens(text):
    """Textual search tokens only, not parsed/elaborated Lean declarations."""
    return [match.group() for match in _TOKEN.finditer(str(text))
            if DECLARATION_NAME.fullmatch(match.group())]


def replace_identifier(text, old, new):
    """Replace an exact token, preserving subscripts and apostrophe distinctions."""
    if any(not isinstance(name, str) or not DECLARATION_NAME.fullmatch(name) for name in (old, new)):
        raise ValueError('Допускаются только полные имена Lean.')
    pattern = re.compile('(?<![' + _BOUNDARY + '])' + re.escape(old) + '(?![' + _BOUNDARY + '])')
    return pattern.subn(lambda _: new, text)
