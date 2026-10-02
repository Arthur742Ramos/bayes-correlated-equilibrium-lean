"""Inventory explicit authored Lean declarations, including attributed defs and named instances."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def strip_comments(source):
    # These sources use no nested block comments; reject a nested opener rather than hide code.
    blocks = re.findall(r'/\-.*?\-/', source, flags=re.S)
    assert all('/-' not in block[2:] for block in blocks), 'Nested comment requires parser review'
    source = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    return re.sub(r'--[^\n]*', '', source)

def authored_names():
    names = []
    files = sorted([*ROOT.glob('*.lean'), *ROOT.glob('BCE/*.lean')])
    for file in files:
        if file.name == 'Challenge.lean':
            continue
        stack = []
        kinds = []
        for line in strip_comments(file.read_text()).splitlines():
            namespace = re.match(r'^namespace\s+(\S+)', line)
            if namespace:
                name = namespace[1]
                stack.append(name if '.' in name or not stack else stack[-1] + '.' + name)
                kinds.append('namespace')
                continue
            if re.match(r'^section(?:\s|$)', line):
                stack.append(stack[-1] if stack else '')
                kinds.append('section')
                continue
            if re.match(r'^end(?:\s|$)', line):
                if stack:
                    stack.pop()
                    kinds.pop()
                continue
            decl = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?'
                            r'(?:def|theorem|lemma|instance)\s+(\w+)', line)
            if decl:
                assert stack, (file, line)
                names.append(stack[-1] + '.' + decl[1])
            elif re.match(r'^(?:noncomputable\s+)?instance\b', line):
                raise AssertionError((file, 'Unnamed instance', line))
    assert len(names) == len(set(names)), 'Duplicate inventory declaration'
    return names

if __name__ == '__main__':
    names = authored_names()
    (ROOT / 'Audit.lean').write_text('module\nimport Solution\n\n' +
        ''.join('#print axioms ' + name + '\n' for name in names))
    print(f'Inventoried {len(names)} authored declarations')
