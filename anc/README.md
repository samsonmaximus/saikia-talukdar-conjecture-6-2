# Ancillary files for "Proof of a conjecture of Saikia and Talukdar on internal 2-adic congruences for overpartition tuples"

All definitions follow M. P. Saikia and P. Talukdar, arXiv:2609.11806v1, Section 6.

## code/ (computational checks, Section 8 of the note)
- `conj62.gp`, `verify1.gp` (PARI/GP 2.15): Conjecture 6.2 and the formula for v_i from the definitions.
- `verify2.py`: independent implementation, exact modulo 2^160 (Clenshaw evaluation of S).
- `ref_check_mod.py`: independent implementation modulo 2^64.
- `ref_check_exact.py` (python-flint): exact big-integer check, including R_{i+1} = Theta(R_i) and the lemmas.
- `lemma.gp`, `base3.gp`, `struct.gp`: closed forms, Lemma 3.3, and the base cases.
- `optcheck.gp`: the congruences directly from the eta-quotient f_2^3/(f_1^2 f_4).
- `independent_check.py [mmax] [N] [mc]`: a short self-contained re-check (pure Python, no libraries): valuations of R_i for even m <= mmax, the congruences directly from the product formula for even m <= mc and 2^i n <= N, and the q-series identities used in Lemma 6.1.

## lean/
- `SaikiaTalukdar.lean`: Lean 4 formalization of Theorem 1.2 (Mathlib, toolchain in `lean-toolchain`).
  Check with `lake env lean SaikiaTalukdar.lean` inside a Lake project depending on Mathlib at the
  matching tag. The file ends with `#print axioms` for the three main theorems; expected output
  `[propext, Classical.choice, Quot.sound]`.
