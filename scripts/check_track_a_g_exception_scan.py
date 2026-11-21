#!/usr/bin/env python3
"""Exhaustive finite referee of actual descending selected-level recursions.

Covers every exception mask, all Boolean decisions of the first scan,
and every modification of those decisions restricted to the exception
set, for scan tops 0..7. It cannot check the genuine Kpt source-profile
premises or substitute for Lean kernel verification.
"""

def stages(top, bits):
    levels = [set() for _ in range(top+1)]
    for i in range(top-1,-1,-1):
        levels[i] = levels[i+1] | ({i} if bits & (1<<i) else set())
    return levels

checked=0
for top in range(8):
    for exception in range(1<<top):
        positions=[i for i in range(top) if exception & (1<<i)]
        for xbits in range(1<<top):
            x=stages(top,xbits)
            for differences in range(1<<len(positions)):
                flips=0
                for j,i in enumerate(positions):
                    if differences & (1<<j):
                        flips |= (1<<i)
                y=stages(top,xbits^flips)
                for stage in range(top+1):
                    assert all((i in x[stage])==(i in y[stage])
                               for i in range(top)
                               if not (exception & (1<<i)))
                assert x[0] ^ y[0] <= set(positions)
                assert len(x[0] ^ y[0]) <= len(positions)
                checked+=1
    print("top",top,"cumulative",checked)
assert checked==335923
print("PASS: 335923 exhaustive exception-localized descending scans")
