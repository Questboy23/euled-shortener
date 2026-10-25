"""ProofOptimizer's proof-length metric, transcribed from arXiv 2510.15700 Appendix L."""
import re
OPS = [':=', '!=', '&&', '-.', '->', '←', '..', '...', '::', ':>', '<;>', ';;', '==', '||', '=>', '<=', '>=', '−1 ', '?_']
SP = [' '.join(c) for c in OPS]; D = dict(zip(SP, OPS))
def lexer(s):
    out = []
    for line in s.splitlines():
        toks, tok = [], ''
        for ch in line:
            if ch == ' ':
                if tok: toks.append(tok); tok = ''
            elif ch.isalnum() or ch in "_.'":
                tok += ch
            else:
                if tok: toks.append(tok); tok = ''
                toks.append(ch)
        if tok: toks.append(tok)
        t = ' '.join(toks)
        for c in SP:
            if c in t: t = t.replace(c, D[c])
        out.append(t)
    return '\n'.join(out)
def remove_statement(s):
    return s.split(":= by", 1)[1].strip() if ":= by" in s else s.split(":=", 1)[1].strip()
def remove_comments(s):
    s = re.sub(r" */-.*-/", "", s, flags=re.DOTALL)
    return re.sub(r" *--.*", "", s)
def proof_length(s):
    try:
        p = lexer(remove_comments(remove_statement(s)))
        return sum(len(l.split(' ')) for l in p.splitlines())
    except Exception:
        return 10**9
def body_only(path):
    """File from the first lemma/theorem on (drops imports, options, namespace header)."""
    t = open(path).read(); m = re.search(r"^(lemma|theorem)\s", t, re.M)
    return t[m.start():] if m else t
