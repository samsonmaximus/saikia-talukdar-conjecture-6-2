import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Saikia–Talukdar, Conjecture 6.2 (arXiv:2609.11806v1, §6)

Let `D_n` be the Chebyshev polynomials of the first kind (`D_0 = 1`, `D_1 = x`,
`D_{n+2} = 2x D_{n+1} - D_n`), `S` the `ℤ`-linear map `x^j ↦ D_{2j}`, `i_m = 1` if `4 ∣ m` and
`i_m = 2` otherwise, `P_{i_m - 1} = x^{m/4}` (if `4 ∣ m`) resp. `D_{m/2}`, `P_{i+1} = S P_i`,
`R_i = (P_i - P_{i-1})/(x - 1)` and `ν(F)` the least 2-adic valuation of a coefficient of `F`.

## Main results

* `conjecture_6_2`: for even `m ≥ 2` and `i > i_m`: `R_i ≠ 0`, `R_i(1) ≠ 0`, `R_i'(1) ≠ 0`,
  `ν₂(R_i'(1)) = ν(R_i)`, `ν₂(R_i(1)) = ν(R_i) + 1` and `ν(R_{i+1}) = ν(R_i) + 3`.
* `nu_R_of_mod4_eq2`, `nu_R_of_four_dvd`: `ν(R_i) = 3i - 8` if `m ≡ 2 (mod 4)` and
  `ν(R_i) = 3i + 2ν₂(m) - 9` if `4 ∣ m`.

## Proof outline

1. `Θ̃(R) := S((x-1)R)/(x-1)` satisfies `R_{i+1} = Θ̃(R_i)` (`R_succ`).
2. With the forward difference `Δ`, `Δ²D_s = 2(x-1)D_{s+1}`, hence `S((x-1)^{2l}) =
   2^l (q-1)^l D_l(q)` and `S((x-1)^{2l+1}) = 2^l (q-1)^{l+1} W_l(q)` with `q = 2x² - 1`
   (`D_{2j} = D_j ∘ q`) and `D_{l+1} - D_l = (x-1) W_l`. This gives the closed form
   `Θ̃((x-1)^k) = 2^{k+1}(x-1)^{⌊k/2⌋}(x+1)^{⌊k/2⌋+1} V_k(q)` (`E'_spec`).
3. In the coordinate `t = x - 1` (`Polynomial.taylor 1`), `Θ̃` becomes `Th` (`taylor_step`);
   `2^{k+1} ∣ Θ̃(t^k)` (`Et_dvd`) and the low-order coefficients give
   `r₀' = 4r₀ + 8r₁`, `r₁' = 2r₀ + 36r₁ + 96r₂ + 64r₃` (`Th_coeff`).
4. Invariant `Good v`: `2^v ∣ R(1+t)`, `r₀ = 2^{v+1}α`, `r₁ = 2^v β`, `α` odd,
   `α + β ≡ 2 (mod 4)`; it is preserved with `v ↦ v + 3` (`good_step`) and yields all claims
   (`good_conclusions`).
5. Base cases: `R(1)` odd ⟹ `Θ̃R` good of level 1 (`good_B1`), used for `m ≡ 2 (mod 4)`
   (`caseA`) and `m ≡ 4 (mod 8)` (`caseB`); for `8 ∣ m`, `R_2 = Θ̃(Q) - Q` with
   `Q = (D_{m/2} - 1)/(x-1)` good of level `2ν₂(m) - 3` by the content bound
   `F_{2N} = 2F_N(F_N + 2)`, `F_N = D_N(1+t) - 1` (`content_bound`, `caseC`).
-/

open Polynomial

namespace SaikiaTalukdar

/-! ## Definitions (faithful to arXiv:2609.11806v1, §6) -/

/-- Chebyshev polynomials of the first kind, written `D_n` in the paper. -/
noncomputable def D : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | (n + 2) => 2 * X * D (n + 1) - D n

/-- The `ℤ`-linear operator with `S (X^j) = D (2 j)`. -/
noncomputable def Sop (A : ℤ[X]) : ℤ[X] := A.sum (fun j a => C a * D (2 * j))

def iM (m : ℕ) : ℕ := if 4 ∣ m then 1 else 2

noncomputable def P0 (m : ℕ) : ℤ[X] := if 4 ∣ m then X ^ (m / 4) else D (m / 2)

/-- `P m i = P_i` for `i ≥ iM m - 1`: `P_{iM m - 1} = P0 m` and `P_{i+1} = S P_i`. -/
noncomputable def P (m i : ℕ) : ℤ[X] := Sop^[i + 1 - iM m] (P0 m)

noncomputable def R (m i : ℕ) : ℤ[X] := (P m i - P m (i - 1)) /ₘ (X - 1)

/-- `ν(F)`: the least 2-adic valuation of a (nonzero) coefficient of `F` (junk value `0` for
`F = 0`). -/
noncomputable def nu (F : ℤ[X]) : ℕ :=
  if h : F.support.Nonempty then
    (F.support.image (fun k => padicValInt 2 (F.coeff k))).min' (h.image _)
  else 0

/-! ## Chebyshev facts -/

@[simp] lemma D_zero : D 0 = 1 := by rw [D]
@[simp] lemma D_one : D 1 = X := by rw [D]
lemma D_add_two (n : ℕ) : D (n + 2) = 2 * X * D (n + 1) - D n := by rw [D]

/-- Two-step induction principle. -/
lemma two_step {p : ℕ → Prop} (h0 : p 0) (h1 : p 1) (h : ∀ n, p n → p (n + 1) → p (n + 2)) :
    ∀ n, p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | (k + 2), ih => exact h k (ih k (by omega)) (ih (k + 1) (by omega))

/-- Product formula `2 D_k D_{n+k} = D_{n+2k} + D_n`. -/
lemma D_prod (k : ℕ) : ∀ n, 2 * D k * D (n + k) = D (n + 2 * k) + D n := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => intro n; simp only [D_zero, add_zero, mul_zero]; ring
    | 1, _ =>
      intro n
      rw [D_one, show n + 2 * 1 = n + 2 by ring, D_add_two]; ring
    | (k + 2), ih =>
      intro n
      have h1 := ih (k + 1) (by omega) (n + 1)
      have h2 := ih k (by omega) (n + 2)
      have e1 := D_add_two (n + 2 * (k + 1))
      have e2 := D_add_two n
      rw [D_add_two k]
      rw [show n + 1 + (k + 1) = n + (k + 2) by ring,
        show n + 1 + 2 * (k + 1) = n + 2 * (k + 1) + 1 by ring] at h1
      rw [show n + 2 + k = n + (k + 2) by ring,
        show n + 2 + 2 * k = n + 2 * (k + 1) by ring] at h2
      rw [show n + 2 * (k + 1) + 2 = n + 2 * (k + 2) by ring] at e1
      linear_combination (2 * X) * h1 - h2 - e1 - e2

/-- `D_{2n} = 2 D_n^2 - 1`. -/
lemma D_double (n : ℕ) : D (2 * n) = 2 * D n ^ 2 - 1 := by
  have h := D_prod n 0
  simp only [zero_add, D_zero] at h
  linear_combination -h

lemma D_two : D 2 = 2 * X ^ 2 - 1 := by
  rw [D_add_two]; simp; ring

/-- `D_{2j} = D_j ∘ (2X^2 - 1)`. -/
lemma D_two_mul_comp : ∀ j, D (2 * j) = (D j).comp (2 * X ^ 2 - 1) := by
  apply two_step
  · simp
  · simp [D_two]
  · intro j h0 h1
    have hp := D_prod 2 (2 * j)
    rw [D_add_two j, sub_comp, mul_comp, mul_comp, X_comp, ← h0, ← h1]
    rw [show 2 * (j + 2) = 2 * j + 2 * 2 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    rw [D_two] at hp
    simp only [ofNat_comp, Nat.cast_ofNat]
    linear_combination -hp

lemma D_eval_one : ∀ n, (D n).eval 1 = 1 := by
  apply two_step
  · simp
  · simp
  · intro n h0 h1
    rw [D_add_two, eval_sub, eval_mul, eval_mul, h0, h1]; simp

/-! ## Taylor coefficients of `D_n` at `1` -/

lemma taylor_two_mul_X_mul (p : ℤ[X]) :
    taylor 1 (2 * X * p) = 2 * X * taylor 1 p + 2 * taylor 1 p := by
  rw [taylor_mul, taylor_mul, taylor_X]
  have : taylor (1 : ℤ) (2 : ℤ[X]) = 2 := by
    rw [show (2 : ℤ[X]) = C 2 by simp, taylor_C]
  rw [this]; simp; ring

lemma tD_rec (n : ℕ) :
    taylor 1 (D (n + 2)) = 2 * X * taylor 1 (D (n + 1)) + 2 * taylor 1 (D (n + 1))
      - taylor 1 (D n) := by
  rw [D_add_two, map_sub, taylor_two_mul_X_mul]

lemma tD_coeff0 (n : ℕ) : (taylor 1 (D n)).coeff 0 = 1 := by
  rw [taylor_coeff_zero, D_eval_one]

lemma tD_coeff1 : ∀ n : ℕ, (taylor 1 (D n)).coeff 1 = (n : ℤ) ^ 2 := by
  apply two_step
  · simp [coeff_one]
  · simp [coeff_one, coeff_X]
  · intro n h0 h1
    rw [tD_rec, coeff_sub, coeff_add, mul_assoc, coeff_ofNat_mul, coeff_X_mul, coeff_ofNat_mul,
      h0, h1, tD_coeff0]
    push_cast; ring

lemma tD_coeff2 : ∀ n : ℕ, 6 * (taylor 1 (D n)).coeff 2 = (n : ℤ) ^ 2 * ((n : ℤ) ^ 2 - 1) := by
  apply two_step
  · simp [coeff_one]
  · simp [coeff_one, coeff_X]
  · intro n h0 h1
    rw [tD_rec, coeff_sub, coeff_add, mul_assoc, coeff_ofNat_mul, coeff_X_mul, coeff_ofNat_mul,
      tD_coeff1]
    push_cast at h0 h1 ⊢
    linear_combination 2 * h1 - h0

/-! ## The operator `S` -/

lemma Sop_add (A B : ℤ[X]) : Sop (A + B) = Sop A + Sop B := by
  unfold Sop
  exact sum_add_index _ _ _ (fun i => by simp) (fun a b₁ b₂ => by simp [add_mul])

lemma Sop_monomial (n : ℕ) (a : ℤ) : Sop (monomial n a) = C a * D (2 * n) := by
  unfold Sop
  exact sum_monomial_index _ _ (by simp)

lemma Sop_zero : Sop 0 = 0 := by simp [Sop]

/-- `S` as an additive homomorphism. -/
noncomputable def SopHom : ℤ[X] →+ ℤ[X] where
  toFun := Sop
  map_zero' := Sop_zero
  map_add' := Sop_add

lemma Sop_sub (A B : ℤ[X]) : Sop (A - B) = Sop A - Sop B := map_sub SopHom A B

lemma Sop_C_mul (c : ℤ) (A : ℤ[X]) : Sop (C c * A) = C c * Sop A := by
  induction A using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, Sop_add, Sop_add, hp, hq, mul_add]
  | monomial n a => rw [C_mul_monomial, Sop_monomial, Sop_monomial, C_mul, mul_assoc]

lemma Sop_X_pow (n : ℕ) : Sop (X ^ n) = D (2 * n) := by
  rw [← monomial_one_right_eq_X_pow, Sop_monomial]; simp

lemma Sop_one : Sop 1 = 1 := by
  simpa using Sop_X_pow 0

lemma Sop_eval_one (A : ℤ[X]) : (Sop A).eval 1 = A.eval 1 := by
  induction A using Polynomial.induction_on' with
  | add p q hp hq => rw [Sop_add, eval_add, eval_add, hp, hq]
  | monomial n a => rw [Sop_monomial, eval_mul, D_eval_one]; simp

/-! ## Forward differences and the closed form of `S((X-1)^n)` -/

/-- Forward difference of a sequence of polynomials. -/
noncomputable def fd (f : ℕ → ℤ[X]) : ℕ → ℤ[X] := fun s => f (s + 1) - f s

lemma fd_apply (f : ℕ → ℤ[X]) (s : ℕ) : fd f s = f (s + 1) - f s := rfl

lemma Sop_X_pow_mul (n : ℕ) :
    ∀ s, Sop (X ^ s * (X - 1) ^ n) = (fd^[n] (fun j => D (2 * j))) s := by
  induction n with
  | zero => intro s; simp [Sop_X_pow]
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply', fd_apply, ← ih, ← ih, ← Sop_sub]
    congr 1; ring

lemma fd_iter_comp (q : ℤ[X]) (f : ℕ → ℤ[X]) (n : ℕ) :
    ∀ s, (fd^[n] (fun j => (f j).comp q)) s = ((fd^[n] f) s).comp q := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fd_apply, fd_apply, ih, ih,
      sub_comp]

lemma fd_iter_mul (c : ℤ[X]) (f : ℕ → ℤ[X]) (n : ℕ) :
    fd^[n] (fun s => c * f s) = fun s => c * (fd^[n] f) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext s; simp only [fd_apply]; ring

lemma fd_iter_shift (f : ℕ → ℤ[X]) (n : ℕ) :
    fd^[n] (fun s => f (s + 1)) = fun s => (fd^[n] f) (s + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext s; simp only [fd_apply]

lemma fd_two_D : fd^[2] D = fun s => 2 * (X - 1) * D (s + 1) := by
  funext s
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fd_apply]
  rw [show s + 1 + 1 = s + 2 by ring, D_add_two]; ring

lemma fd_even_D (l : ℕ) : fd^[2 * l] D = fun s => 2 ^ l * (X - 1) ^ l * D (s + l) := by
  induction l with
  | zero => funext s; simp
  | succ l ih =>
    rw [show 2 * (l + 1) = 2 * l + 2 by ring, Function.iterate_add_apply, fd_two_D,
      fd_iter_mul, fd_iter_shift, ih]
    funext s
    simp only []
    rw [show s + 1 + l = s + (l + 1) by ring]; ring

lemma fd_odd_D (l s : ℕ) :
    (fd^[2 * l + 1] D) s = 2 ^ l * (X - 1) ^ l * (D (s + l + 1) - D (s + l)) := by
  rw [Function.iterate_succ_apply', fd_apply, fd_even_D]
  simp only
  rw [show s + 1 + l = s + l + 1 by ring]; ring

/-- `W_l = (D_{l+1} - D_l)/(X - 1)` (Chebyshev polynomials of the fourth kind). -/
noncomputable def W : ℕ → ℤ[X]
  | 0 => 1
  | 1 => 2 * X + 1
  | (n + 2) => 2 * X * W (n + 1) - W n

@[simp] lemma W_zero : W 0 = 1 := by rw [W]
@[simp] lemma W_one : W 1 = 2 * X + 1 := by rw [W]
lemma W_add_two (n : ℕ) : W (n + 2) = 2 * X * W (n + 1) - W n := by rw [W]

lemma D_succ_sub : ∀ n, D (n + 1) - D n = (X - 1) * W n := by
  apply two_step
  · simp
  · rw [D_two]; simp; ring
  · intro n h0 h1
    show D (n + 3) - D (n + 2) = (X - 1) * W (n + 2)
    have h1' : D (n + 2) - D (n + 1) = (X - 1) * W (n + 1) := h1
    have e1 : D (n + 3) = 2 * X * D (n + 2) - D (n + 1) := D_add_two (n + 1)
    have e2 : D (n + 2) = 2 * X * D (n + 1) - D n := D_add_two n
    have e3 : W (n + 2) = 2 * X * W (n + 1) - W n := W_add_two n
    linear_combination e1 - (X - 1) * e3 + 2 * X * h1' - h0 - e2

/-- The polynomial `2X^2 - 1`. -/
noncomputable abbrev q2 : ℤ[X] := 2 * X ^ 2 - 1

lemma Sop_sub_one_pow (n : ℕ) : Sop ((X - 1) ^ n) = ((fd^[n] D) 0).comp q2 := by
  have h := Sop_X_pow_mul n 0
  rw [pow_zero, one_mul] at h
  rw [h, ← fd_iter_comp]
  have : (fun j => D (2 * j)) = (fun j => (D j).comp q2) := funext D_two_mul_comp
  rw [this]

/-- The closed form of `Θ̃((X-1)^k)` in the `x`-coordinate. -/
noncomputable def E' (k : ℕ) : ℤ[X] :=
  2 ^ (k + 1) * (X - 1) ^ (k / 2) * (X + 1) ^ (k / 2 + 1) *
    (if Even k then W (k / 2) else D (k / 2 + 1)).comp q2

lemma E'_even (l : ℕ) :
    E' (2 * l) = 2 ^ (2 * l + 1) * (X - 1) ^ l * (X + 1) ^ (l + 1) * (W l).comp q2 := by
  have h1 : 2 * l / 2 = l := by omega
  simp [E', h1]

lemma E'_odd (l : ℕ) :
    E' (2 * l + 1) = 2 ^ (2 * l + 2) * (X - 1) ^ l * (X + 1) ^ (l + 1) * (D (l + 1)).comp q2 := by
  have h1 : (2 * l + 1) / 2 = l := by omega
  have h2 : ¬ Even (2 * l + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one l
  unfold E'
  rw [ite_eq_right h2, h1]

lemma q2_sub_one : q2 - 1 = 2 * (X - 1) * (X + 1) := by
  simp only [q2]; ring

lemma X_sub_one_comp_q2 : (X - 1 : ℤ[X]).comp q2 = 2 * (X - 1) * (X + 1) := by
  rw [sub_comp, X_comp, one_comp, q2_sub_one]

/-- Key identity: `(X - 1) Θ̃((X-1)^k) = S((X-1)^(k+1))`. -/
lemma E'_spec (k : ℕ) : (X - 1) * E' k = Sop ((X - 1) ^ (k + 1)) := by
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [Sop_sub_one_pow, fd_odd_D, E'_even]
    simp only [zero_add]
    rw [D_succ_sub]
    simp only [mul_comp, pow_comp, X_sub_one_comp_q2, ofNat_comp, Nat.cast_ofNat, mul_pow]
    ring
  · rw [show 2 * l + 1 + 1 = 2 * (l + 1) by ring, Sop_sub_one_pow, fd_even_D, E'_odd]
    simp only [mul_comp, pow_comp, X_sub_one_comp_q2, zero_add, ofNat_comp, Nat.cast_ofNat,
      mul_pow]
    ring

/-! ## The coordinate `t = X - 1` -/

lemma taylor_X_sub_one : taylor (1 : ℤ) (X - 1) = X := by simp

lemma taylor_ofNat (n : ℕ) [n.AtLeastTwo] :
    taylor (1 : ℤ) (OfNat.ofNat n : ℤ[X]) = OfNat.ofNat n := by
  rw [← C_ofNat, taylor_C]

@[simp] lemma taylor_two' : taylor (1 : ℤ) (2 : ℤ[X]) = 2 := taylor_ofNat 2

lemma taylor_X_add_one : taylor (1 : ℤ) (X + 1) = X + 2 := by
  simp; ring

lemma comp_taylor (F : ℤ[X]) : (taylor 1 F).comp (X - 1) = F := by
  rw [taylor_apply, comp_assoc]; simp

lemma taylor_comp (G : ℤ[X]) : taylor 1 (G.comp (X - 1)) = G := by
  rw [taylor_apply, comp_assoc]; simp

lemma taylor_q2_comp_eval_zero (V : ℤ[X]) : (taylor 1 (V.comp q2)).eval 0 = V.eval 1 := by
  rw [taylor_eval, eval_comp]; simp

/-- `Θ̃((X-1)^k)` written in the coordinate `t = X - 1`. -/
noncomputable def Et (k : ℕ) : ℤ[X] := taylor 1 (E' k)

lemma Et_even (l : ℕ) :
    Et (2 * l) = 2 ^ (2 * l + 1) * X ^ l * (X + 2) ^ (l + 1) * taylor 1 ((W l).comp q2) := by
  unfold Et
  rw [E'_even]
  simp only [taylor_mul, taylor_pow, taylor_X_sub_one, taylor_X_add_one, taylor_two']

lemma Et_odd (l : ℕ) :
    Et (2 * l + 1) =
      2 ^ (2 * l + 2) * X ^ l * (X + 2) ^ (l + 1) * taylor 1 ((D (l + 1)).comp q2) := by
  unfold Et
  rw [E'_odd]
  simp only [taylor_mul, taylor_pow, taylor_X_sub_one, taylor_X_add_one, taylor_two']

/-- Lemma (a): `2^(k+1)` divides every coefficient of `Θ̃(t^k)`. -/
lemma Et_dvd (k : ℕ) : (2 : ℤ[X]) ^ (k + 1) ∣ Et k := by
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [Et_even, mul_assoc, mul_assoc]; exact dvd_mul_right _ _
  · rw [Et_odd, mul_assoc, mul_assoc]; exact dvd_mul_right _ _

lemma Et_zero : Et 0 = 2 * X + 4 := by
  have h := Et_even 0
  simp only [mul_zero, zero_add, pow_one, pow_zero, mul_one, W_zero, one_comp] at h
  rw [h]; simp; ring

lemma Et_one : Et 1 = 8 * X ^ 3 + 32 * X ^ 2 + 36 * X + 8 := by
  have h := Et_odd 0
  simp only [mul_zero, zero_add, pow_one, pow_zero, mul_one, D_one, X_comp] at h
  rw [h]
  simp only [q2, map_sub, taylor_mul, taylor_two', taylor_pow, taylor_X, map_one]
  simp; ring

lemma Et_two : Et 2 = X * (8 * (X + 2) ^ 2 * taylor 1 ((W 1).comp q2)) := by
  have h := Et_even 1
  rw [h]; ring

lemma Et_three : Et 3 = X * (16 * (X + 2) ^ 2 * taylor 1 ((D 2).comp q2)) := by
  have h := Et_odd 1
  rw [h]; ring

lemma Et_ge_four (k : ℕ) (hk : 4 ≤ k) : ∃ K, Et k = X ^ 2 * K := by
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 2 := ⟨l - 2, by omega⟩
    exact ⟨2 ^ (2 * (l' + 2) + 1) * X ^ l' * (X + 2) ^ (l' + 2 + 1) *
      taylor 1 ((W (l' + 2)).comp q2), by rw [Et_even]; ring⟩
  · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 2 := ⟨l - 2, by omega⟩
    exact ⟨2 ^ (2 * (l' + 2) + 2) * X ^ l' * (X + 2) ^ (l' + 2 + 1) *
      taylor 1 ((D (l' + 2 + 1)).comp q2), by rw [Et_odd]; ring⟩

/-- Low-order coefficients of `Θ̃(t^k)` (Lemma (b)). -/
def c0 : ℕ → ℤ
  | 0 => 4
  | 1 => 8
  | _ => 0

def c1 : ℕ → ℤ
  | 0 => 2
  | 1 => 36
  | 2 => 96
  | 3 => 64
  | _ => 0

lemma Et_coeff (k : ℕ) : (Et k).coeff 0 = c0 k ∧ (Et k).coeff 1 = c1 k := by
  match k with
  | 0 => rw [Et_zero]; simp [c0, c1, coeff_X]
  | 1 => rw [Et_one]; simp [c0, c1, coeff_X, coeff_X_pow]
  | 2 =>
    refine ⟨?_, ?_⟩
    · rw [Et_two, coeff_X_mul_zero]; rfl
    · rw [Et_two, coeff_X_mul, coeff_zero_eq_eval_zero, eval_mul, taylor_q2_comp_eval_zero]
      simp [c1]
  | 3 =>
    refine ⟨?_, ?_⟩
    · rw [Et_three, coeff_X_mul_zero]; rfl
    · rw [Et_three, coeff_X_mul, coeff_zero_eq_eval_zero, eval_mul, taylor_q2_comp_eval_zero,
        D_eval_one]
      simp [c1]
  | k + 4 =>
    obtain ⟨K, hK⟩ := Et_ge_four (k + 4) (by omega)
    rw [hK, coeff_X_pow_mul', coeff_X_pow_mul']
    simp [c0, c1]

/-! ## The operator `Θ̃` in the coordinate `t` -/

/-- `Th G = Σ_k g_k Θ̃(t^k)`, i.e. `Θ̃` written in the coordinate `t = X - 1`. -/
noncomputable def Th (G : ℤ[X]) : ℤ[X] := G.sum (fun k a => C a * Et k)

lemma Th_add (A B : ℤ[X]) : Th (A + B) = Th A + Th B := by
  unfold Th
  exact sum_add_index _ _ _ (fun i => by simp) (fun a b₁ b₂ => by simp [add_mul])

lemma Th_monomial (n : ℕ) (a : ℤ) : Th (monomial n a) = C a * Et n := by
  unfold Th
  exact sum_monomial_index _ _ (by simp)

lemma Th_zero : Th 0 = 0 := by simp [Th]

noncomputable def ThHom : ℤ[X] →+ ℤ[X] where
  toFun := Th
  map_zero' := Th_zero
  map_add' := Th_add

lemma Th_sub (A B : ℤ[X]) : Th (A - B) = Th A - Th B := map_sub ThHom A B

lemma Th_C_mul (c : ℤ) (A : ℤ[X]) : Th (C c * A) = C c * Th A := by
  induction A using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, Th_add, Th_add, hp, hq, mul_add]
  | monomial n a => rw [C_mul_monomial, Th_monomial, Th_monomial, C_mul, mul_assoc]

lemma Th_two_pow_mul (v : ℕ) (A : ℤ[X]) : Th (2 ^ v * A) = 2 ^ v * Th A := by
  have h : (2 : ℤ[X]) ^ v = C (2 ^ v) := by simp
  rw [h, Th_C_mul]

/-- The transfer identity: `Th` really is `Θ̃` in the coordinate `t`. -/
lemma transfer (G : ℤ[X]) : (X - 1) * (Th G).comp (X - 1) = Sop ((X - 1) * G.comp (X - 1)) := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq => rw [Th_add, add_comp, mul_add, hp, hq, add_comp, mul_add, Sop_add]
  | monomial n a =>
    rw [Th_monomial, mul_comp, C_comp, Et, comp_taylor, monomial_comp,
      show (X - 1) * (C a * (X - 1) ^ n) = C a * (X - 1) ^ (n + 1) by ring, Sop_C_mul,
      ← E'_spec]
    ring

lemma X_sub_one_ne_zero : (X - 1 : ℤ[X]) ≠ 0 := by
  simpa using X_sub_C_ne_zero (1 : ℤ)

/-- If `(X - 1) F' = S((X - 1) F)` then, in the coordinate `t`, `F' = Th F`. -/
lemma taylor_step {F F' : ℤ[X]} (h : (X - 1) * F' = Sop ((X - 1) * F)) :
    taylor 1 F' = Th (taylor 1 F) := by
  have ht := transfer (taylor 1 F)
  rw [comp_taylor] at ht
  rw [← ht] at h
  rw [mul_left_cancel₀ X_sub_one_ne_zero h, taylor_comp]

/-! ## The sequences `P_i` and `R_i` -/

lemma iM_pos (m : ℕ) : 1 ≤ iM m := by unfold iM; split_ifs <;> omega

lemma P_succ (m i : ℕ) (hi : iM m ≤ i + 1) : P m (i + 1) = Sop (P m i) := by
  unfold P
  rw [show i + 1 + 1 - iM m = (i + 1 - iM m) + 1 by omega, Function.iterate_succ_apply']

lemma R_spec (m i : ℕ) (hi : iM m ≤ i) : (X - 1) * R m i = P m i - P m (i - 1) := by
  have hP : P m i = Sop (P m (i - 1)) := by
    have := P_succ m (i - 1) (by omega)
    rwa [show i - 1 + 1 = i by have := iM_pos m; omega] at this
  have hroot : IsRoot (P m i - P m (i - 1)) 1 := by
    rw [IsRoot, eval_sub, hP, Sop_eval_one, sub_self]
  have h := (mul_divByMonic_eq_iff_isRoot (p := P m i - P m (i - 1)) (a := 1)).mpr hroot
  have hC : (X - C 1 : ℤ[X]) = X - 1 := by simp
  rw [hC] at h
  exact h

lemma R_succ (m i : ℕ) (hi : iM m ≤ i) : (X - 1) * R m (i + 1) = Sop ((X - 1) * R m i) := by
  rw [R_spec m (i + 1) (by omega), R_spec m i hi, Sop_sub, Nat.add_sub_cancel,
    P_succ m i (by omega)]
  have := P_succ m (i - 1) (by omega)
  rw [show i - 1 + 1 = i by have := iM_pos m; omega] at this
  rw [this]

lemma taylor_R_succ (m i : ℕ) (hi : iM m ≤ i) :
    taylor 1 (R m (i + 1)) = Th (taylor 1 (R m i)) :=
  taylor_step (R_succ m i hi)

/-! ## Low-order coefficients and divisibility for `Th` -/

lemma Th_coeff (G : ℤ[X]) :
    (Th G).coeff 0 = 4 * G.coeff 0 + 8 * G.coeff 1 ∧
    (Th G).coeff 1 = 2 * G.coeff 0 + 36 * G.coeff 1 + 96 * G.coeff 2 + 64 * G.coeff 3 := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Th_add, coeff_add, hp.1, hq.1, hp.2, hq.2]
    constructor <;> ring
  | monomial n a =>
    rw [Th_monomial, coeff_C_mul, coeff_C_mul, (Et_coeff n).1, (Et_coeff n).2]
    simp only [coeff_monomial]
    match n with
    | 0 => simp [c0, c1, mul_comm]
    | 1 => simp [c0, c1, mul_comm]
    | 2 => simp [c0, c1, mul_comm]
    | 3 => simp [c0, c1, mul_comm]
    | k + 4 => simp [c0, c1]

lemma two_dvd_Th (G : ℤ[X]) : (2 : ℤ[X]) ∣ Th G := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq => rw [Th_add]; exact dvd_add hp hq
  | monomial n a =>
    rw [Th_monomial]
    exact Dvd.dvd.mul_left (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero n)) (Et_dvd n)) _

lemma eight_dvd_Th_X_sq_mul (H : ℤ[X]) : (2 : ℤ[X]) ^ 3 ∣ Th (X ^ 2 * H) := by
  induction H using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, Th_add]; exact dvd_add hp hq
  | monomial n a =>
    rw [X_pow_mul_monomial, Th_monomial]
    exact Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow 2 (by omega)) (Et_dvd (n + 2))) _

lemma Th_X_sq_dvd (v : ℕ) (H : ℤ[X]) (hH : (2 : ℤ[X]) ^ v ∣ H) :
    (2 : ℤ[X]) ^ (v + 3) ∣ Th (X ^ 2 * H) := by
  obtain ⟨K, rfl⟩ := hH
  rw [show X ^ 2 * (2 ^ v * K) = 2 ^ v * (X ^ 2 * K) by ring, Th_two_pow_mul, pow_add]
  exact mul_dvd_mul_left _ (eight_dvd_Th_X_sq_mul K)

lemma decomp (G : ℤ[X]) : G = C (G.coeff 0) + C (G.coeff 1) * X + X ^ 2 * divX (divX G) := by
  have h1 := X_mul_divX_add G
  have h2 := X_mul_divX_add (divX G)
  rw [coeff_divX, zero_add] at h2
  linear_combination -h1 - X * h2

lemma two_pow_dvd_iff (v : ℕ) (G : ℤ[X]) :
    (2 : ℤ[X]) ^ v ∣ G ↔ ∀ k, (2 : ℤ) ^ v ∣ G.coeff k := by
  rw [show (2 : ℤ[X]) ^ v = C (2 ^ v) by simp, C_dvd_iff_dvd_coeff]

lemma taylor_two_any (r : ℤ) : taylor r (2 : ℤ[X]) = 2 := by
  rw [← C_ofNat, taylor_C]

lemma two_pow_dvd_taylor_iff (v : ℕ) (F : ℤ[X]) :
    (2 : ℤ[X]) ^ v ∣ taylor 1 F ↔ (2 : ℤ[X]) ^ v ∣ F := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨taylor (-1) K, ?_⟩
    have : F = taylor (-1) (taylor 1 F) := by rw [taylor_taylor]; simp
    rw [this, hK, taylor_mul, taylor_pow, taylor_two_any]
  · rintro ⟨K, rfl⟩
    exact ⟨taylor 1 K, by rw [taylor_mul, taylor_pow, taylor_two']⟩

/-! ## The invariant "good of level `v`" (in the coordinate `t`) -/

/-- `G = Σ r_k t^k` is good of level `v`: `2^v ∣ G`, `r_0 = 2^(v+1) α`, `r_1 = 2^v β`
with `α` odd and `α + β ≡ 2 (mod 4)` (so `β` is odd too). -/
def Good (v : ℕ) (G : ℤ[X]) : Prop :=
  (2 : ℤ[X]) ^ v ∣ G ∧ ∃ α β : ℤ, G.coeff 0 = 2 ^ (v + 1) * α ∧ G.coeff 1 = 2 ^ v * β ∧
    (α + β) % 4 = 2 ∧ α % 2 = 1

/-- The induction step: good of level `v` ⟹ `Θ̃` of it is good of level `v + 3`. -/
lemma good_step {v : ℕ} {G : ℤ[X]} (hG : Good v G) : Good (v + 3) (Th G) := by
  obtain ⟨hdiv, α, β, h0, h1, hab, hα⟩ := hG
  have hc := (two_pow_dvd_iff v G).1 hdiv
  obtain ⟨ρ2, hρ2⟩ := hc 2
  obtain ⟨ρ3, hρ3⟩ := hc 3
  obtain ⟨tc0, tc1⟩ := Th_coeff G
  obtain ⟨q, hq⟩ : ∃ q, α + β = 4 * q + 2 := ⟨(α + β) / 4, by omega⟩
  refine ⟨?_, 2 * q + 1, 2 * q + 1 + 4 * β + 12 * ρ2 + 8 * ρ3, ?_, ?_, ?_, ?_⟩
  · have e0 : Th (C (G.coeff 0)) = C (G.coeff 0) * Et 0 := by
      have := Th_monomial 0 (G.coeff 0); rwa [monomial_zero_left] at this
    have e1 : Th (C (G.coeff 1) * X) = C (G.coeff 1) * Et 1 := by
      rw [C_mul_X_eq_monomial, Th_monomial]
    rw [decomp G, Th_add, Th_add, e0, e1]
    refine dvd_add ?_ (Th_X_sq_dvd v _ ?_)
    · rw [Et_zero, Et_one, h0, h1]
      have hα' : α = 4 * q + 2 - β := by omega
      refine ⟨C (4 * q + 2) + C (2 * q + 1 + 4 * β) * X + C (4 * β) * X ^ 2 + C β * X ^ 3, ?_⟩
      rw [hα']
      simp only [map_mul, map_pow, map_add, map_sub, map_ofNat, map_one]
      ring
    · rw [two_pow_dvd_iff]; intro k; rw [coeff_divX, coeff_divX]; exact hc _
  · rw [tc0, h0, h1]; linear_combination (2 : ℤ) ^ (v + 3) * hq
  · rw [tc1, h0, h1, hρ2, hρ3]; linear_combination (4 * (2 : ℤ) ^ v) * hq
  · omega
  · omega

/-- Base case B1: if `R(1)` is odd then `Θ̃ R` is good of level `1`. -/
lemma good_B1 {G : ℤ[X]} (hG : G.coeff 0 % 2 = 1) : Good 1 (Th G) := by
  obtain ⟨tc0, tc1⟩ := Th_coeff G
  refine ⟨by simpa using two_dvd_Th G, G.coeff 0 + 2 * G.coeff 1,
    G.coeff 0 + 18 * G.coeff 1 + 48 * G.coeff 2 + 32 * G.coeff 3, ?_, ?_, ?_, ?_⟩
  · rw [tc0]; ring
  · rw [tc1]; ring
  · omega
  · omega

lemma good_sub {v : ℕ} {G H : ℤ[X]} (hG : Good v G) (hH : (2 : ℤ[X]) ^ (v + 3) ∣ H) :
    Good v (H - G) := by
  obtain ⟨hdiv, α, β, h0, h1, hab, hα⟩ := hG
  have hc := (two_pow_dvd_iff (v + 3) H).1 hH
  obtain ⟨a0, ha0⟩ := hc 0
  obtain ⟨a1, ha1⟩ := hc 1
  refine ⟨dvd_sub (dvd_trans (pow_dvd_pow 2 (by omega)) hH) hdiv, 4 * a0 - α, 8 * a1 - β,
    ?_, ?_, ?_, ?_⟩
  · rw [coeff_sub, ha0, h0]; ring
  · rw [coeff_sub, ha1, h1]; ring
  · omega
  · omega

/-! ## From the invariant to the statements about `ν` -/

lemma padicValInt_two_pow_mul {w : ℕ} {β : ℤ} (hβ : β % 2 = 1) :
    padicValInt 2 (2 ^ w * β) = w := by
  have hne : (2 : ℤ) ^ w * β ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (by omega)
  have h1 : w ≤ padicValInt 2 (2 ^ w * β) := by
    rcases (padicValInt_dvd_iff (p := 2) w (2 ^ w * β)).1
      (by push_cast; exact dvd_mul_right _ _) with h | h
    · exact absurd h hne
    · exact h
  have h2 : ¬ (w + 1 ≤ padicValInt 2 (2 ^ w * β)) := by
    intro h
    have := (padicValInt_dvd_iff (p := 2) (w + 1) (2 ^ w * β)).2 (Or.inr h)
    push_cast at this
    rw [pow_succ] at this
    have := (mul_dvd_mul_iff_left (pow_ne_zero w (two_ne_zero' ℤ))).1 this
    omega
  omega

lemma le_nu_iff {F : ℤ[X]} (hF : F ≠ 0) (v : ℕ) :
    v ≤ nu F ↔ ∀ k, (2 : ℤ) ^ v ∣ F.coeff k := by
  have hne : F.support.Nonempty := support_nonempty.2 hF
  unfold nu
  rw [dite_eq_left hne, Finset.le_min'_iff]
  constructor
  · intro h k
    by_cases hk : F.coeff k = 0
    · rw [hk]; exact dvd_zero _
    · have h' := h _ (Finset.mem_image_of_mem _ (mem_support_iff.2 hk))
      have := (padicValInt_dvd_iff (p := 2) v (F.coeff k)).2 (Or.inr h')
      simpa using this
  · intro h y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    rcases (padicValInt_dvd_iff (p := 2) v (F.coeff k)).1 (by simpa using h k) with h0 | h0
    · exact absurd h0 (mem_support_iff.1 hk)
    · exact h0

lemma nu_eq {F : ℤ[X]} (hF : F ≠ 0) {v : ℕ} (h1 : ∀ k, (2 : ℤ) ^ v ∣ F.coeff k)
    (h2 : ∃ k, ¬ (2 : ℤ) ^ (v + 1) ∣ F.coeff k) : nu F = v := by
  have a := (le_nu_iff hF v).2 h1
  have b : ¬ (v + 1 ≤ nu F) := fun h => by
    obtain ⟨k, hk⟩ := h2
    exact hk ((le_nu_iff hF (v + 1)).1 h k)
  omega

lemma good_conclusions {v : ℕ} {F : ℤ[X]} (h : Good v (taylor 1 F)) :
    F ≠ 0 ∧ F.eval 1 ≠ 0 ∧ (derivative F).eval 1 ≠ 0 ∧
    padicValInt 2 ((derivative F).eval 1) = v ∧ padicValInt 2 (F.eval 1) = v + 1 ∧
    nu F = v := by
  obtain ⟨hdiv, α, β, h0, h1, hab, hα⟩ := h
  rw [taylor_coeff_zero] at h0
  rw [taylor_coeff_one] at h1
  have hβ : β % 2 = 1 := by omega
  have hev : F.eval 1 ≠ 0 := by
    rw [h0]; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (by omega)
  have hF : F ≠ 0 := fun hF => hev (by rw [hF, eval_zero])
  refine ⟨hF, hev, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (by omega)
  · rw [h1]; exact padicValInt_two_pow_mul hβ
  · rw [h0]; exact padicValInt_two_pow_mul hα
  · apply nu_eq hF
    · exact (two_pow_dvd_iff v F).1 ((two_pow_dvd_taylor_iff v F).1 hdiv)
    · by_contra hcon
      simp only [not_exists, not_not] at hcon
      have h3 : (2 : ℤ[X]) ^ (v + 1) ∣ taylor 1 F :=
        (two_pow_dvd_taylor_iff _ F).2 ((two_pow_dvd_iff _ F).2 hcon)
      have h4 := (two_pow_dvd_iff _ _).1 h3 1
      rw [taylor_coeff_one, h1, pow_succ] at h4
      have := (mul_dvd_mul_iff_left (pow_ne_zero v (two_ne_zero' ℤ))).1 h4
      omega

/-! ## Base cases -/

lemma good_iter {m i0 v : ℕ} (hi0 : iM m ≤ i0) (h : Good v (taylor 1 (R m i0))) :
    ∀ j, Good (v + 3 * j) (taylor 1 (R m (i0 + j))) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [show i0 + (j + 1) = (i0 + j) + 1 by ring, taylor_R_succ m (i0 + j) (by omega),
      show v + 3 * (j + 1) = (v + 3 * j) + 3 by ring]
    exact good_step ih

lemma four_dvd_taylor_Sop_coeff1 (A : ℤ[X]) : (4 : ℤ) ∣ (taylor 1 (Sop A)).coeff 1 := by
  induction A using Polynomial.induction_on' with
  | add p q hp hq => rw [Sop_add, map_add, coeff_add]; exact dvd_add hp hq
  | monomial n a =>
    rw [Sop_monomial, taylor_mul, taylor_C, coeff_C_mul, tD_coeff1]
    exact Dvd.dvd.mul_left ⟨(n : ℤ) ^ 2, by push_cast; ring⟩ _

lemma iM_of_mod4_2 {m : ℕ} (hm : m % 4 = 2) : iM m = 2 := by
  unfold iM; rw [ite_eq_right (by omega)]

lemma iM_of_four_dvd {m : ℕ} (hm : 4 ∣ m) : iM m = 1 := by
  unfold iM; rw [ite_eq_left hm]

lemma P_base (m : ℕ) : P m (iM m - 1) = P0 m := by
  unfold P
  rw [show iM m - 1 + 1 - iM m = 0 by have := iM_pos m; omega]
  rfl

/-- Case `m ≡ 2 (mod 4)`: `R_3` is good of level `1`. -/
lemma caseA (m : ℕ) (hm : m % 4 = 2) : Good 1 (taylor 1 (R m 3)) := by
  have hiM := iM_of_mod4_2 hm
  have hP1 : P m 1 = D (m / 2) := by
    have h := P_base m
    rw [hiM] at h
    rw [h, P0, ite_eq_right (by omega)]
  have hR2 : (X - 1) * R m 2 = Sop (D (m / 2)) - D (m / 2) := by
    rw [R_spec m 2 (by omega), show 2 - 1 = 1 from rfl, P_succ m 1 (by omega), hP1]
  have hc : (taylor 1 (R m 2)).coeff 0 % 2 = 1 := by
    have h := congrArg (fun F => (taylor 1 F).coeff 1) hR2
    rw [taylor_mul, taylor_X_sub_one, coeff_X_mul, map_sub, coeff_sub, tD_coeff1] at h
    obtain ⟨K, hK⟩ := four_dvd_taylor_Sop_coeff1 (D (m / 2))
    rw [hK] at h
    obtain ⟨t, ht⟩ : ∃ t, m / 2 = 2 * t + 1 := ⟨m / 2 / 2, by omega⟩
    rw [h, ht]
    push_cast
    have : 4 * K - (2 * (t : ℤ) + 1) ^ 2 = 2 * (2 * K - 2 * (t : ℤ) ^ 2 - 2 * t - 1) + 1 := by ring
    rw [this]; omega
  have := taylor_R_succ m 2 (by omega)
  rw [show 2 + 1 = 3 from rfl] at this
  rw [this]
  exact good_B1 hc

/-- Case `m ≡ 4 (mod 8)`: `R_2` is good of level `1`. -/
lemma caseB (m : ℕ) (hm : m % 8 = 4) : Good 1 (taylor 1 (R m 2)) := by
  have h4 : 4 ∣ m := by omega
  have hiM := iM_of_four_dvd h4
  have hP0 : P m 0 = X ^ (m / 4) := by
    have h := P_base m
    rw [hiM] at h
    rw [h, P0, ite_eq_left h4]
  have hR1 : (X - 1) * R m 1 = D (2 * (m / 4)) - X ^ (m / 4) := by
    rw [R_spec m 1 (by omega), show 1 - 1 = 0 from rfl, P_succ m 0 (by omega), hP0, Sop_X_pow]
  have hc : (taylor 1 (R m 1)).coeff 0 % 2 = 1 := by
    have h := congrArg (fun F => (taylor 1 F).coeff 1) hR1
    rw [taylor_mul, taylor_X_sub_one, coeff_X_mul, map_sub, coeff_sub, tD_coeff1,
      taylor_X_pow, C_1, coeff_X_add_one_pow] at h
    obtain ⟨t, ht⟩ : ∃ t, m / 4 = 2 * t + 1 := ⟨m / 4 / 2, by omega⟩
    rw [h, ht]
    push_cast
    simp only [Nat.choose_one_right]
    push_cast
    have : (2 * (2 * (t : ℤ) + 1)) ^ 2 - (2 * t + 1) =
      2 * (8 * (t : ℤ) ^ 2 + 7 * t + 1) + 1 := by ring
    rw [this]; omega
  have := taylor_R_succ m 1 (by omega)
  rw [this]
  exact good_B1 hc

/-- The content bound (referee's fix): `2^(2a+1)` divides `T_{2^(a+1) u}(1 + t) - 1`, via
`F_{2N} = 2 F_N (F_N + 2)`. -/
lemma content_bound (u : ℕ) : ∀ a : ℕ,
    (2 : ℤ[X]) ^ (2 * a + 1) ∣ taylor 1 (D (2 ^ (a + 1) * u)) - 1 := by
  intro a
  induction a with
  | zero =>
    rw [show 2 ^ (0 + 1) * u = 2 * u by ring, D_double]
    refine ⟨taylor 1 (D u) ^ 2 - 1, ?_⟩
    rw [map_sub, taylor_mul, taylor_pow, taylor_two', taylor_one, C_1]
    ring
  | succ a ih =>
    obtain ⟨K, hK⟩ := ih
    rw [show 2 ^ (a + 1 + 1) * u = 2 * (2 ^ (a + 1) * u) by ring, D_double]
    have hN : taylor 1 (D (2 ^ (a + 1) * u)) = 2 ^ (2 * a + 1) * K + 1 := by
      linear_combination hK
    refine ⟨K * (2 ^ (2 * a) * K + 1), ?_⟩
    rw [map_sub, taylor_mul, taylor_pow, hN, taylor_two', taylor_one, C_1]
    ring

lemma X_sub_one_mul_comp (G : ℤ[X]) : (X - 1) * G.comp (X - 1) = (X * G).comp (X - 1) := by
  rw [mul_comp, X_comp]

lemma odd_sq_mod_eight {u : ℕ} (hu : u % 2 = 1) : ((u : ℤ) ^ 2) % 8 = 1 := by
  obtain ⟨w, rfl⟩ : ∃ w, u = 2 * w + 1 := ⟨u / 2, by omega⟩
  obtain ⟨r, hr⟩ := Nat.even_mul_succ_self w
  have : ((2 * w + 1 : ℕ) : ℤ) ^ 2 = 4 * ((w * (w + 1) : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [this, hr]; push_cast; omega

/-- Case `8 ∣ m` (base case B2): `R_2` is good of level `2 ν(m/4) + 1`. -/
lemma caseC (m : ℕ) (hm : m % 8 = 0) (hm0 : m ≠ 0) :
    ∃ b u : ℕ, m / 4 = 2 ^ (b + 1) * u ∧ u % 2 = 1 ∧ Good (2 * b + 3) (taylor 1 (R m 2)) := by
  have h4 : 4 ∣ m := by omega
  have hiM := iM_of_four_dvd h4
  have hn0 : m / 4 ≠ 0 := by omega
  obtain ⟨a, u, hu, hnu⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hu2 : u % 2 = 1 := Nat.odd_iff.1 hu
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := by
    refine ⟨a - 1, ?_⟩
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp at hnu; omega
    · omega
  refine ⟨b, u, hnu, hu2, ?_⟩
  -- notation
  set n := m / 4 with hn
  have hP0 : P m 0 = X ^ n := by
    have h := P_base m
    rw [hiM] at h
    rw [h, P0, ite_eq_left h4]
  have hR1 : (X - 1) * R m 1 = D (2 * n) - X ^ n := by
    rw [R_spec m 1 (by omega), show 1 - 1 = 0 from rfl, P_succ m 0 (by omega), hP0, Sop_X_pow]
  have hN : 2 * n = 2 ^ (b + 1 + 1) * u := by rw [hnu]; ring
  have hcont := content_bound u (b + 1)
  rw [← hN, show 2 * (b + 1) + 1 = 2 * b + 3 by ring] at hcont
  set p := taylor 1 (D (2 * n)) - 1 with hp
  have hp0 : p.coeff 0 = 0 := by rw [hp, coeff_sub, tD_coeff0, coeff_one_zero, sub_self]
  set GQ := divX p with hGQ
  have hXGQ : X * GQ = p := by
    have := X_mul_divX_add p
    rw [hp0, C_0, add_zero] at this
    exact this
  have hcp := (two_pow_dvd_iff _ p).1 hcont
  -- `Q = (T_{2n} - 1)/(X - 1)` is good of level `2b + 3`
  have hgood : Good (2 * b + 3) GQ := by
    refine ⟨(two_pow_dvd_iff _ GQ).2 (fun k => by rw [hGQ, coeff_divX]; exact hcp _), ?_⟩
    have e0 : GQ.coeff 0 = ((2 * n : ℕ) : ℤ) ^ 2 := by
      rw [hGQ, coeff_divX, hp, coeff_sub, tD_coeff1, coeff_one]; simp
    have e1 : 6 * GQ.coeff 1 = ((2 * n : ℕ) : ℤ) ^ 2 * (((2 * n : ℕ) : ℤ) ^ 2 - 1) := by
      rw [hGQ, coeff_divX, hp, coeff_sub, mul_sub, tD_coeff2, coeff_one]; simp
    obtain ⟨β, hβ⟩ : (2 : ℤ) ^ (2 * b + 3) ∣ GQ.coeff 1 := by
      rw [hGQ, coeff_divX]; exact hcp _
    rw [hβ, hN] at e1
    rw [hN] at e0
    push_cast at e0 e1
    have e : (2 : ℤ) ^ (2 * b + 4) * (3 * β) =
        2 ^ (2 * b + 4) * ((u : ℤ) ^ 2 * (2 ^ (2 * b + 4) * (u : ℤ) ^ 2 - 1)) := by
      linear_combination e1
    have e3 := mul_left_cancel₀ (pow_ne_zero (2 * b + 4) (two_ne_zero' ℤ)) e
    have hs := odd_sq_mod_eight hu2
    refine ⟨(u : ℤ) ^ 2, β, ?_, hβ, ?_, by omega⟩
    · rw [e0]; ring
    · have e4 : 3 * β = 16 * (2 ^ (2 * b) * ((u : ℤ) ^ 2) ^ 2) - (u : ℤ) ^ 2 := by
        rw [e3]; ring
      generalize (u : ℤ) ^ 2 = s at hs e4 ⊢
      generalize 2 ^ (2 * b) * s ^ 2 = y at e4
      omega
  -- `Θ̃((X^n - 1)/(X - 1)) = Q`
  have hτR1 : X * taylor 1 (R m 1) = taylor 1 (D (2 * n)) - (X + 1) ^ n := by
    have h := congrArg (taylor (1 : ℤ)) hR1
    rwa [taylor_mul, taylor_X_sub_one, map_sub, taylor_X_pow, C_1] at h
  have hB : Th (GQ - taylor 1 (R m 1)) = GQ := by
    have hstep : (X - 1) * GQ.comp (X - 1) =
        Sop ((X - 1) * (GQ - taylor 1 (R m 1)).comp (X - 1)) := by
      rw [X_sub_one_mul_comp, X_sub_one_mul_comp, mul_sub, hXGQ, hτR1, hp]
      rw [show taylor 1 (D (2 * n)) - 1 - (taylor 1 (D (2 * n)) - (X + 1) ^ n) =
        (X + 1) ^ n - 1 by ring]
      rw [sub_comp, comp_taylor, one_comp, sub_comp, pow_comp, add_comp, X_comp, one_comp,
        sub_add_cancel, Sop_sub, Sop_X_pow, Sop_one]
    have := taylor_step hstep
    rw [taylor_comp, taylor_comp] at this
    exact this.symm
  have hR2 : taylor 1 (R m 2) = Th GQ - GQ := by
    rw [taylor_R_succ m 1 (by omega), show taylor 1 (R m 1) = GQ - (GQ - taylor 1 (R m 1)) by ring,
      Th_sub, hB]
  rw [hR2]
  exact good_sub hgood (good_step hgood).1

/-! ## Coverage: `R_i` is good for every `i > iM m` -/

lemma good_of_mod4_eq2 {m : ℕ} (hm : m % 4 = 2) {i : ℕ} (hi : 2 < i) :
    Good (3 * i - 8) (taylor 1 (R m i)) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = 3 + j := ⟨i - 3, by omega⟩
  have := good_iter (m := m) (i0 := 3) (by rw [iM_of_mod4_2 hm]; omega) (caseA m hm) j
  rwa [show 3 * (3 + j) - 8 = 1 + 3 * j by omega]

lemma good_of_mod8_eq4 {m : ℕ} (hm : m % 8 = 4) {i : ℕ} (hi : 1 < i) :
    Good (3 * i - 5) (taylor 1 (R m i)) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = 2 + j := ⟨i - 2, by omega⟩
  have := good_iter (m := m) (i0 := 2) (by rw [iM_of_four_dvd (by omega)]; omega) (caseB m hm) j
  rwa [show 3 * (2 + j) - 5 = 1 + 3 * j by omega]

lemma good_of_mod8_eq0 {m : ℕ} (hm : m % 8 = 0) (hm0 : m ≠ 0) {i : ℕ} (hi : 1 < i) :
    ∃ b u : ℕ, m / 4 = 2 ^ (b + 1) * u ∧ u % 2 = 1 ∧
      Good (2 * b + 3 + 3 * (i - 2)) (taylor 1 (R m i)) := by
  obtain ⟨b, u, h1, h2, h3⟩ := caseC m hm hm0
  obtain ⟨j, rfl⟩ : ∃ j, i = 2 + j := ⟨i - 2, by omega⟩
  refine ⟨b, u, h1, h2, ?_⟩
  have := good_iter (m := m) (i0 := 2) (by rw [iM_of_four_dvd (by omega)]; omega) h3 j
  rwa [show 2 + j - 2 = j by omega]

lemma exists_good (m : ℕ) (hm : Even m) (hm2 : 2 ≤ m) (i : ℕ) (hi : iM m < i) :
    ∃ v, Good v (taylor 1 (R m i)) := by
  have hm' := Nat.even_iff.1 hm
  rcases (by omega : m % 4 = 2 ∨ m % 8 = 4 ∨ m % 8 = 0) with h | h | h
  · rw [iM_of_mod4_2 h] at hi
    exact ⟨_, good_of_mod4_eq2 h hi⟩
  · rw [iM_of_four_dvd (by omega)] at hi
    exact ⟨_, good_of_mod8_eq4 h hi⟩
  · rw [iM_of_four_dvd (by omega)] at hi
    obtain ⟨b, u, -, -, hg⟩ := good_of_mod8_eq0 h (by omega) hi
    exact ⟨_, hg⟩

/-! ## Main theorem -/

/-- **Conjecture 6.2** of Saikia–Talukdar (arXiv:2609.11806v1): for every even `m ≥ 2` and every
`i > i_m`, `ν(R_i'(1)) = ν(R_i)`, `ν(R_i(1)) = ν(R_i) + 1` and `ν(R_{i+1}) = ν(R_i) + 3`
(together with the non-vanishing needed for these valuations to be meaningful). -/
theorem conjecture_6_2 (m : ℕ) (hm : Even m) (hm2 : 2 ≤ m) (i : ℕ) (hi : iM m < i) :
    R m i ≠ 0 ∧ (R m i).eval 1 ≠ 0 ∧ (derivative (R m i)).eval 1 ≠ 0 ∧
    padicValInt 2 ((derivative (R m i)).eval 1) = nu (R m i) ∧
    padicValInt 2 ((R m i).eval 1) = nu (R m i) + 1 ∧
    nu (R m (i + 1)) = nu (R m i) + 3 := by
  obtain ⟨v, hv⟩ := exists_good m hm hm2 i hi
  have hv' : Good (v + 3) (taylor 1 (R m (i + 1))) := by
    rw [taylor_R_succ m i (by omega)]; exact good_step hv
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := good_conclusions hv
  obtain ⟨-, -, -, -, -, h6'⟩ := good_conclusions hv'
  exact ⟨h1, h2, h3, by rw [h4, h6], by rw [h5, h6], by rw [h6', h6]⟩

/-! ## The explicit value of `ν(R_i)` -/

/-- `ν(R_i) = 3i - 8` when `m ≡ 2 (mod 4)` and `i > i_m = 2`. -/
theorem nu_R_of_mod4_eq2 {m : ℕ} (hm : m % 4 = 2) {i : ℕ} (hi : iM m < i) :
    (nu (R m i) : ℤ) = 3 * i - 8 := by
  rw [iM_of_mod4_2 hm] at hi
  rw [(good_conclusions (good_of_mod4_eq2 hm hi)).2.2.2.2.2]
  omega

/-- `ν(R_i) = 3i + 2ν₂(m) - 9` when `4 ∣ m`, `m ≠ 0` and `i > i_m = 1`. -/
theorem nu_R_of_four_dvd {m : ℕ} (hm : 4 ∣ m) (hm0 : m ≠ 0) {i : ℕ} (hi : iM m < i) :
    (nu (R m i) : ℤ) = 3 * i + 2 * padicValNat 2 m - 9 := by
  rw [iM_of_four_dvd hm] at hi
  rcases (by omega : m % 8 = 4 ∨ m % 8 = 0) with h | h
  · have hv : padicValNat 2 m = 2 := by
      obtain ⟨t, ht⟩ : ∃ t, m = 2 ^ 2 * (2 * t + 1) := ⟨m / 8, by omega⟩
      rw [ht, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by omega)]
    rw [(good_conclusions (good_of_mod8_eq4 h hi)).2.2.2.2.2, hv]
    omega
  · obtain ⟨b, u, h1, h2, h3⟩ := good_of_mod8_eq0 h hm0 hi
    have hv : padicValNat 2 m = b + 3 := by
      have hm' : m = 2 ^ (b + 3) * u := by
        have := Nat.div_mul_cancel hm
        rw [← this, h1]; ring
      rw [hm', padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by omega)]
    rw [(good_conclusions h3).2.2.2.2.2, hv]
    omega

/-! ## Sanity checks on small cases (independent of the main proof) -/

lemma D_three : D 3 = 4 * X ^ 3 - 3 * X := by
  have h : D 3 = 2 * X * D 2 - D 1 := D_add_two 1
  rw [h, D_two, D_one]; ring

lemma D_four : D 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 := by
  have h : D 4 = 2 * X * D 3 - D 2 := D_add_two 2
  rw [h, D_three, D_two]; ring

/-- `m = 2`, `i = 3`: `R_3 = 16x^3 + 16x^2 - 2x - 2`. -/
lemma R_2_3 : R 2 3 = 16 * X ^ 3 + 16 * X ^ 2 - 2 * X - 2 := by
  have hiM : iM 2 = 2 := by decide
  have hP1 : P 2 1 = X := by
    have h := P_base 2
    rw [hiM] at h
    rw [h, P0, ite_eq_right (by decide)]
    exact D_one
  have hP2 : P 2 2 = D 2 := by
    rw [P_succ 2 1 (by rw [hiM]), hP1, ← pow_one X, Sop_X_pow]
  have hP3 : P 2 3 = 16 * X ^ 4 - 16 * X ^ 2 + 1 := by
    rw [P_succ 2 2 (by rw [hiM]; omega), hP2, D_two, Sop_sub, Sop_one,
      show (2 : ℤ[X]) * X ^ 2 = C 2 * X ^ 2 by simp, Sop_C_mul, Sop_X_pow, D_four]
    simp; ring
  have h := R_spec 2 3 (by rw [hiM]; omega)
  rw [show 3 - 1 = 2 from rfl, hP3, hP2, D_two] at h
  apply mul_left_cancel₀ X_sub_one_ne_zero
  rw [h]; ring

/-- `m = 8`, `i = 2`: `R_2 = 1024x^7 + 1024x^6 - 1024x^5 - 1024x^4 + 184x^3 + 184x^2`. -/
lemma R_8_2 : R 8 2 = 1024 * X ^ 7 + 1024 * X ^ 6 - 1024 * X ^ 5 - 1024 * X ^ 4
    + 184 * X ^ 3 + 184 * X ^ 2 := by
  have hiM : iM 8 = 1 := by decide
  have hP0 : P 8 0 = X ^ 2 := by
    have h := P_base 8
    rw [hiM] at h
    rw [h, P0, ite_eq_left (by decide)]
  have hP1 : P 8 1 = D 4 := by
    rw [P_succ 8 0 (by rw [hiM]), hP0, Sop_X_pow]
  have hD8 : D 8 = 2 * (8 * X ^ 4 - 8 * X ^ 2 + 1) ^ 2 - 1 := by
    have h : D 8 = 2 * D 4 ^ 2 - 1 := D_double 4
    rw [h, D_four]
  have hP2 : P 8 2 = 1024 * X ^ 8 - 2048 * X ^ 6 + 1216 * X ^ 4 - 192 * X ^ 2 + 1 := by
    rw [P_succ 8 1 (by rw [hiM]; omega), hP1, D_four, Sop_add, Sop_sub, Sop_one,
      show (8 : ℤ[X]) * X ^ 4 = C 8 * X ^ 4 by simp, show (8 : ℤ[X]) * X ^ 2 = C 8 * X ^ 2 by simp,
      Sop_C_mul, Sop_C_mul, Sop_X_pow, Sop_X_pow, show 2 * 4 = 8 from rfl,
      show 2 * 2 = 4 from rfl, hD8, D_four]
    simp; ring
  have h := R_spec 8 2 (by rw [hiM]; omega)
  rw [show 2 - 1 = 1 from rfl, hP2, hP1, D_four] at h
  apply mul_left_cancel₀ X_sub_one_ne_zero
  rw [h]; ring

/-- Direct check for `m = 2`, `i = 3` (`i_m = 2`): `ν(R_3) = 1`, `R_3(1) = 28 = 2^2·7`,
`R_3'(1) = 78 = 2·39`, matching `ν(R_i) = 3i - 8`. -/
example : nu (R 2 3) = 1 ∧ (R 2 3).eval 1 = 28 ∧ (derivative (R 2 3)).eval 1 = 78 ∧
    (nu (R 2 3) : ℤ) = 3 * 3 - 8 := by
  refine ⟨?_, ?_, ?_, nu_R_of_mod4_eq2 (by norm_num) (by decide)⟩
  · rw [R_2_3]
    have hF : (16 * X ^ 3 + 16 * X ^ 2 - 2 * X - 2 : ℤ[X]) ≠ 0 := by
      intro h; have := congrArg (eval 1) h; norm_num at this
    refine nu_eq hF ((two_pow_dvd_iff 1 _).1 ⟨8 * X ^ 3 + 8 * X ^ 2 - X - 1, by ring⟩) ⟨0, ?_⟩
    rw [coeff_zero_eq_eval_zero]; norm_num
  · rw [R_2_3]; norm_num
  · rw [R_2_3]; simp

/-- Direct check for `m = 8`, `i = 2` (`i_m = 1`): `ν(R_2) = 3`, `R_2(1) = 368 = 2^4·23`,
`R_2'(1) = 5016 = 2^3·627`, matching `ν(R_i) = 3i + 2ν(m) - 9`. -/
example : nu (R 8 2) = 3 ∧ (R 8 2).eval 1 = 368 ∧ (derivative (R 8 2)).eval 1 = 5016 ∧
    (nu (R 8 2) : ℤ) = 3 * 2 + 2 * 3 - 9 := by
  have hv : padicValNat 2 8 = 3 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  refine ⟨?_, ?_, ?_, by rw [nu_R_of_four_dvd (by norm_num) (by norm_num) (by decide), hv]; norm_num⟩
  · rw [R_8_2]
    have hF : (1024 * X ^ 7 + 1024 * X ^ 6 - 1024 * X ^ 5 - 1024 * X ^ 4 + 184 * X ^ 3
        + 184 * X ^ 2 : ℤ[X]) ≠ 0 := by
      intro h; have := congrArg (eval 1) h; norm_num at this
    refine nu_eq hF ((two_pow_dvd_iff 3 _).1 ⟨128 * X ^ 7 + 128 * X ^ 6 - 128 * X ^ 5
      - 128 * X ^ 4 + 23 * X ^ 3 + 23 * X ^ 2, by ring⟩) ⟨2, ?_⟩
    simp [coeff_X_pow]
  · rw [R_8_2]; norm_num
  · rw [R_8_2]; simp

end SaikiaTalukdar

#print axioms SaikiaTalukdar.conjecture_6_2
#print axioms SaikiaTalukdar.nu_R_of_mod4_eq2
#print axioms SaikiaTalukdar.nu_R_of_four_dvd
