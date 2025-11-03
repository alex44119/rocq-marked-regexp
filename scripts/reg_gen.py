def coq_reg_from_string(s: str) -> str:
    """
    Convert a regexp string into a Coq Reg expression as a string.
    Always parenthesizes subexpressions to produce valid Coq syntax.
    """

    # Helper: parse level 3 (alternation)
    def parse_L3(s):
        parts = []
        depth = 0
        last = 0
        for i, c in enumerate(s):
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            elif c == '|' and depth == 0:
                parts.append(s[last:i])
                last = i+1
        if parts:
            parts.append(s[last:])
            expr = parse_L2(parts[-1])
            for part in reversed(parts[:-1]):
                expr = f"(Alt ({parse_L2(part)}) ({expr}))"
            return expr
        else:
            return parse_L2(s)

    # Helper: parse level 2 (sequence)
    def parse_L2(s):
        units = []
        i = 0
        while i < len(s):
            if s[i] == '(':
                depth = 1
                j = i + 1
                while j < len(s) and depth > 0:
                    if s[j] == '(':
                        depth += 1
                    elif s[j] == ')':
                        depth -= 1
                    j += 1
                units.append(s[i:j])
                i = j
            elif s[i] == 'ε':
                units.append('ε')
                i += 1
            else:
                units.append(s[i])
                i += 1
            # Include '*' with previous unit
            if i < len(s) and s[i] == '*':
                units[-1] += '*'
                i += 1

        expr = parse_L1(units[-1])
        for unit in reversed(units[:-1]):
            expr = f"(Seq ({parse_L1(unit)}) ({expr}))"
        return expr

    # Helper: parse level 1 (repetition)
    def parse_L1(s):
        if s.endswith('*'):
            inner = parse_L1(s[:-1])
            return f"(Rep ({inner}))"
        return parse_L0(s)

    # Helper: parse level 0 (atomic)
    def parse_L0(s):
        s = s.strip()
        if s == 'ε':
            return 'Eps'
        elif s.startswith('(') and s.endswith(')'):
            return parse_L3(s[1:-1])
        elif len(s) == 1:
            return f'Sym "{s}"%char'
        else:
            raise ValueError(f"Cannot parse atomic: {s}")

    return parse_L3(s)


if __name__ == "__main__":
    s = input("Enter regexp string: ")
    print(coq_reg_from_string(s))
