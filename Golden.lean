import CottLean

/-!
# The Fibonacci substitution on traction pairs

Null Theory's combinatorial core, stated on cott-lean's unreduced pairs. The row `ω² = 1 + ω` of
`qtimes` is ℤ[φ] (discriminant 5). A word over {A, B} is counted as a pair `T(#A, #B)`, with `A` the
letter `ω = T(1,0)` and `B` the letter `0 = T(0,1)`, so counting a word is the mediant of its letters.

What comes out, every line a theorem for every word or pair:

* the substitution `A ↦ AB, B ↦ A` is multiplication by `ω` in that row (`counts_sigma`), and its matrix
  `qmat 1 1 ω` is Stevens' `M = [[1,1],[1,0]]` (`qmat_omega`);
* the step is total: the word `B`, ratio `0/1`, goes to `A`, ratio `1/0`, with no `x ≠ 0` exclusion
  (`sigma_B`, `step_zero`), where the ratio map `μ(x) = 1 + 1/x` has to exclude it;
* `σⁿ⁺²(A) = σⁿ⁺¹(A) ++ σⁿ(A)`: each iterate holds the earlier ones whole (`sigma_iterate_append`);
* the counts of `σⁿ(A)` are `T(F(n+1), F(n))` (`counts_sigma_iterate`);
* the norm is multiplicative and `N(ω) = -1`, so the counts carry the parity `(-1)ⁿ⁺¹` (Cassini)
  (`gnorm_counts_sigma_iterate`): the determinant `-1` grading is the norm of `ω`;
* the Galois flip `φ ↔ ψ` is a pair map, and a pair times its flip lands on `T(0, N)` (`gtimes_gconj`).
-/

namespace T.Golden

open T

/-- ℤ[φ] on the pairs: `T(p,q)` read as `q + p·ω` with `ω² = 1 + ω`. -/
def gtimes (x y : T) : T := qtimes 1 1 x y

/-- The norm of `q + p·ω` in ℤ[φ], the determinant of multiplying by the pair (`det_qmat` at `a = b = 1`). -/
def gnorm (x : T) : ℤ := x.q ^ 2 + x.p * x.q - x.p ^ 2

/-- The Galois flip `ω ↦ 1 - ω`, that is `φ ↦ ψ`, on the pair. -/
def gconj (x : T) : T := ⟨-x.p, x.q + x.p⟩

/-! ## The matrix -/

/-- Multiplying by `ω` in the golden row is Stevens' substitution matrix. -/
theorem qmat_omega : qmat 1 1 «ω» = !![1, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qmat, «ω»]

theorem gnorm_omega : gnorm «ω» = -1 := by simp [gnorm, «ω»]

theorem gnorm_gtimes (x y : T) : gnorm (gtimes x y) = gnorm x * gnorm y := by
  simp only [gnorm, gtimes, qtimes]; ring

/-- The step on a pair: `T(p, q) ↦ T(p + q, p)`. -/
theorem gtimes_omega (x : T) : gtimes x «ω» = ⟨x.p + x.q, x.p⟩ := by
  ext <;> simp [gtimes, qtimes, «ω»] <;> ring

/-- `0` steps to `ω`: the ratio `0/1` goes to `1/0`, a pair like any other. -/
theorem step_zero : gtimes «0» «ω» = «ω» := by
  rw [gtimes_omega]; ext <;> simp [«0», «ω»]

/-- `ω` steps to `1`, since `ω² = 1 + ω`. -/
theorem step_omega : gtimes «ω» «ω» = «1» := by
  rw [gtimes_omega]; ext <;> simp [«ω», «1»]

/-! ## Words -/

/-- The substitution on words over {A, B}, with `A = true` and `B = false`. -/
def sigma : List Bool → List Bool
  | [] => []
  | true :: w => true :: false :: sigma w
  | false :: w => true :: sigma w

/-- A letter as a pair: `A` is `ω = T(1,0)`, `B` is `0 = T(0,1)`. -/
def letter : Bool → T
  | true => «ω»
  | false => «0»

/-- The letter counts `T(#A, #B)`: the mediant of the letters, from the unit `0ω`. -/
def counts : List Bool → T
  | [] => «0ω»
  | a :: w => letter a ⊕ counts w

theorem counts_append (u v : List Bool) : counts (u ++ v) = counts u ⊕ counts v := by
  induction u with
  | nil => ext <;> simp [counts, oplus, «0ω»]
  | cons a u ih =>
    simp only [List.cons_append, counts, ih]
    ext <;> simp [oplus] <;> ring

theorem sigma_append (u v : List Bool) : sigma (u ++ v) = sigma u ++ sigma v := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [sigma, ih]

/-- The substitution counted is multiplication by `ω` in the golden row. -/
theorem counts_sigma (w : List Bool) : counts (sigma w) = gtimes (counts w) «ω» := by
  rw [gtimes_omega]
  induction w with
  | nil => ext <;> simp [sigma, counts, «0ω»]
  | cons a w ih =>
    cases a <;> simp only [sigma, counts, letter] <;> rw [ih] <;>
      ext <;> simp [oplus, «ω», «0»] <;> ring

/-- The word `B` goes to `A`: ratio `0` to ratio `1/0`, where `μ(x) = 1 + 1/x` needs `x ≠ 0`. -/
theorem sigma_B : sigma [false] = [true] ∧ counts [false] = «0» ∧ counts [true] = «ω» := by
  refine ⟨rfl, ?_, ?_⟩ <;> ext <;> simp [counts, letter, oplus, «0», «ω», «0ω»]

/-- Every iterate holds the two before it, whole: `σⁿ⁺²(A) = σⁿ⁺¹(A) ++ σⁿ(A)`. -/
theorem sigma_iterate_append (n : ℕ) :
    sigma^[n + 2] [true] = sigma^[n + 1] [true] ++ sigma^[n] [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : sigma^[n + 1 + 2] [true] = sigma (sigma^[n + 2] [true]) :=
      Function.iterate_succ_apply' _ _ _
    have h2 : sigma^[n + 1 + 1] [true] = sigma (sigma^[n + 1] [true]) :=
      Function.iterate_succ_apply' _ _ _
    have h3 : sigma^[n + 1] [true] = sigma (sigma^[n] [true]) := Function.iterate_succ_apply' _ _ _
    conv_lhs => rw [h1, ih, sigma_append]
    rw [← h2, ← h3]

/-- The counts of `σⁿ(A)` are consecutive Fibonacci numbers. -/
theorem counts_sigma_iterate (n : ℕ) :
    counts (sigma^[n] [true]) = ⟨(Nat.fib (n + 1) : ℤ), (Nat.fib n : ℤ)⟩ := by
  induction n with
  | zero =>
    have : counts [true] = «ω» := by ext <;> simp [counts, letter, oplus, «ω», «0ω»]
    simpa [«ω»] using this
  | succ n ih =>
    rw [Function.iterate_succ_apply', counts_sigma, ih, gtimes_omega]
    ext <;> simp [Nat.fib_add_two] <;> ring

/-- The determinant `-1` grading: the norm of `σⁿ(A)`'s counts is `(-1)ⁿ⁺¹`, which is Cassini's identity. -/
theorem gnorm_counts_sigma_iterate (n : ℕ) : gnorm (counts (sigma^[n] [true])) = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp [counts, letter, gnorm, oplus, «ω», «0ω»]
  | succ n ih =>
    rw [Function.iterate_succ_apply', counts_sigma, gnorm_gtimes, ih, gnorm_omega]; ring

/-- Cassini, read off: `F(n)² + F(n+1)F(n) - F(n+1)² = (-1)ⁿ⁺¹`. -/
theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) ^ 2 + Nat.fib (n + 1) * Nat.fib n - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  have h := gnorm_counts_sigma_iterate n
  rw [counts_sigma_iterate] at h
  simpa [gnorm] using h

/-! ## The Galois flip -/

theorem gconj_gconj (x : T) : gconj (gconj x) = x := by
  ext <;> simp [gconj]

/-- A pair times its flip lands on `T(0, N)`: the norm, as a pair. -/
theorem gtimes_gconj (x : T) : gtimes x (gconj x) = ⟨0, gnorm x⟩ := by
  ext <;> simp [gtimes, qtimes, gconj, gnorm] <;> ring

/-- The flip reverses the norm's sign on `ω`, and multiplying by `ω` undoes exactly: `N(ω) = -1` is a unit. -/
theorem gtimes_omega_gconj_omega : gtimes «ω» (gconj «ω») = «_0» := by
  ext <;> simp [gtimes, qtimes, gconj, «ω», «_0»]

/-! ## The flipped matrix: the ring of three's walker

The walker of the ring of three writes the older digit minus the newer, `g(n+2) = g(n) - g(n+1)`. Its
matrix on `(older, newer)` is `[[0,1],[1,-1]]`. It is the substitution's own inverse: multiplying by
`_1 = T(1,-1)`, which is `ω - 1 = 1/φ` in this row. The walker is the Fibonacci step walked backward, and
its sequence is the Fibonacci numbers with every other one negated. On the ring of three both matrices lap
in 8.
-/

/-- The walker's matrix is multiplication by `_1` in the golden row. -/
theorem qmat_underOne : qmat 1 1 «_1» = !![0, 1; 1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qmat, «_1»]

/-- The walker's matrix is the substitution matrix's inverse, both ways round. -/
theorem walker_mul_sigma : !![0, 1; 1, -1] * !![1, 1; 1, 0] = (1 : Matrix (Fin 2) (Fin 2) ℤ) ∧
    !![1, 1; 1, 0] * !![0, 1; 1, -1] = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Multiplying by `_1` undoes the substitution's step on every pair: `ω · _1 = 0`, the unit. -/
theorem gtimes_omega_underOne : gtimes «ω» «_1» = «0» := by
  ext <;> simp [gtimes, qtimes, «ω», «_1», «0»]

theorem step_back (x : T) : gtimes (gtimes x «ω») «_1» = x := by
  ext <;> simp [gtimes, qtimes, «ω», «_1»]

/-- Fibonacci with every other term negated runs "older minus newer". -/
theorem flipped_fib (n : ℕ) :
    (-1 : ℤ) ^ (n + 2) * Nat.fib (n + 2) =
      (-1) ^ n * Nat.fib n - (-1) ^ (n + 1) * Nat.fib (n + 1) := by
  rw [Nat.fib_add_two]; push_cast; ring

/-- On the ring of three, the substitution matrix laps in exactly 8. -/
theorem sigma_mod3_lap : (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 8 = 1 ∧
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 4 ≠ 1 := by
  decide

/-- So does the walker. -/
theorem walker_mod3_lap : (!![0, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 8 = 1 ∧
    (!![0, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 4 ≠ 1 := by
  decide

/-! ## The empty word: ∅ at every depth

Null Theory seeds the substitution with `∅`, the empty word. On the pairs its count is `0ω = T(0,0)`,
the traction `0/0`. It is not left behind by the first step: `σ` keeps it at every depth, it sits inside
every word's count as the mediant's unit, and every golden product it touches lands on it.
-/

/-- The empty word survives every step: `σⁿ(ε) = ε`. -/
theorem sigma_iterate_nil (n : ℕ) : sigma^[n] [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- Its count is `0ω = T(0,0)`, the traction `0/0`. -/
theorem counts_nil : counts [] = «0ω» := rfl

/-- It is inside every word, at every depth: each iterate is itself with ε on either side, and its
count carries ε's count as the mediant's unit. -/
theorem nil_in_every_iterate (n : ℕ) :
    sigma^[n] [true] = [] ++ sigma^[n] [true] ++ [] ∧
      counts (sigma^[n] [true]) = counts [] ⊕ counts (sigma^[n] [true]) := by
  refine ⟨by simp, ?_⟩
  rw [counts_nil]; ext <;> simp [oplus, «0ω»]

/-- And every golden product it touches lands on it. -/
theorem gtimes_zeroOmega (x : T) : gtimes «0ω» x = «0ω» ∧ gtimes x «0ω» = «0ω» := by
  constructor <;> ext <;> simp [gtimes, qtimes, «0ω»]

end T.Golden
