import Foldlaw

/-!
# The birth function

For distinct imaginary basis units `e_p, e_q` of the Cayley–Dickson algebra
`CD m`, the anti-associator `W(e_p,e_q)(e_r) = (e_p e_r) e_q + e_p (e_r e_q)`
sends every basis unit `e_r` to `(±1 ± 1)·e_{p⊕q⊕r}`. Hence

  `dim ker W(e_p,e_q) = #{ r : (e_p, e_r, e_q) does not associate }`.

This file computes that count exactly, at every level, by a recursion on
the doubling (BDI 2005, Lemmas 8.9/8.10 cover two of the six cases; the
other four — `(a,0),(0,a)`, `(a,0),(0,1)`, `(0,a),(0,b)`, `(0,1),(0,b)` —
are proved here), and seals the result: `finrank ker W(e_p,e_q) = birth p q`.
-/

namespace Foldlaw
open CD

/-! ## Floor A: equality up to sign, and the index xor -/

/-- Equal up to sign. -/
def Same {m : ℕ} (a b : CD m) : Prop := a = b ∨ a = neg b

theorem Same.refl {m : ℕ} {a : CD m} : Same a a := Or.inl (Eq.refl a)

theorem Same.symm {m : ℕ} {a b : CD m} (h : Same a b) : Same b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

theorem Same.trans {m : ℕ} {a b c : CD m} (h1 : Same a b) (h2 : Same b c) :
    Same a c := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h1.trans h2)
  · exact Or.inr (h1.trans h2)
  · exact Or.inr (by rw [h1, h2])
  · exact Or.inl (by rw [h1, h2, neg_neg])

theorem Same.neg_right {m : ℕ} {a b : CD m} (h : Same a b) : Same a (neg b) := by
  rcases h with h | h
  · exact Or.inr (by rw [neg_neg]; exact h)
  · exact Or.inl h

theorem Same.neg_left {m : ℕ} {a b : CD m} (h : Same a b) : Same (neg a) b :=
  h.symm.neg_right.symm

theorem Same.mul_right {m : ℕ} {a b : CD m} (c : CD m) (h : Same a b) :
    Same (a * c) (b * c) := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, neg_mul])

theorem Same.mul_left {m : ℕ} {a b : CD m} (c : CD m) (h : Same a b) :
    Same (c * a) (c * b) := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, mul_neg])

theorem Same.mul {m : ℕ} {a b c d : CD m} (h1 : Same a b) (h2 : Same c d) :
    Same (a * c) (b * d) :=
  (h1.mul_right c).trans (h2.mul_left b)

theorem Same.conj {m : ℕ} {a b : CD m} (h : Same a b) : Same (conj a) (conj b) := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, conj_neg])

theorem Same.dblL {m : ℕ} {a b : CD m} (h : Same a b) :
    Same (dbl a (cdZero : CD m)) (dbl b (cdZero : CD m)) := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, neg_dbl, neg_zero])

theorem Same.dblU {m : ℕ} {a b : CD m} (h : Same a b) :
    Same (dbl (cdZero : CD m) a) (dbl (cdZero : CD m) b) := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, neg_dbl, neg_zero])

/-- Conjugation is a sign on every basis unit. -/
theorem same_conj_beval {m : ℕ} (u : BUnit m) : Same (conj (beval u)) (beval u) :=
  basisUnit_conj (beval_basis u)

/-- The four products of the doubling, on slots. -/
theorem mul_LL {n : ℕ} (u v : CD n) :
    dbl u (cdZero : CD n) * dbl v (cdZero : CD n) = dbl (u * v) (cdZero : CD n) := by
  show dbl (u * v - (cdZero : CD n) * conj (cdZero : CD n))
      (conj u * (cdZero : CD n) + v * (cdZero : CD n))
    = dbl (u * v) (cdZero : CD n)
  simp only [zero_mul, sub_zero, mul_zero, add_zero]

theorem mul_LU {n : ℕ} (u v : CD n) :
    dbl u (cdZero : CD n) * dbl (cdZero : CD n) v = dbl (cdZero : CD n) (conj u * v) := by
  show dbl (u * (cdZero : CD n) - v * conj (cdZero : CD n))
      (conj u * v + (cdZero : CD n) * (cdZero : CD n))
    = dbl (cdZero : CD n) (conj u * v)
  simp only [mul_zero, conj_zero, sub_zero, add_zero]

theorem mul_UL {n : ℕ} (u v : CD n) :
    dbl (cdZero : CD n) u * dbl v (cdZero : CD n) = dbl (cdZero : CD n) (v * u) := by
  show dbl ((cdZero : CD n) * v - (cdZero : CD n) * conj u)
      (conj (cdZero : CD n) * (cdZero : CD n) + v * u)
    = dbl (cdZero : CD n) (v * u)
  simp only [conj_zero, zero_mul, mul_zero, sub_zero, zero_add]

theorem mul_UU {n : ℕ} (u v : CD n) :
    dbl (cdZero : CD n) u * dbl (cdZero : CD n) v
      = dbl (neg (v * conj u)) (cdZero : CD n) := by
  show dbl ((cdZero : CD n) * (cdZero : CD n) - v * conj u)
      (conj (cdZero : CD n) * v + (cdZero : CD n) * u)
    = dbl (neg (v * conj u)) (cdZero : CD n)
  simp only [zero_mul, mul_zero, conj_zero, add_zero, cdZero_sub]

/-- The xor of two indices: the index of the product of the units. -/
def bxor : ∀ {m : ℕ}, BUnit m → BUnit m → BUnit m
  | 0, BUnit.real0, BUnit.real0 => BUnit.real0
  | _ + 1, BUnit.lower u, BUnit.lower v => BUnit.lower (bxor u v)
  | _ + 1, BUnit.lower u, BUnit.upper v => BUnit.upper (bxor u v)
  | _ + 1, BUnit.upper u, BUnit.lower v => BUnit.upper (bxor u v)
  | _ + 1, BUnit.upper u, BUnit.upper v => BUnit.lower (bxor u v)

/-- The index of 1. -/
def bone : ∀ m : ℕ, BUnit m
  | 0 => BUnit.real0
  | m + 1 => BUnit.lower (bone m)

theorem beval_bone (m : ℕ) : beval (bone m) = (cdOne : CD m) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    show dbl (beval (bone n)) (cdZero : CD n) = dbl cdOne cdZero
    rw [ih]

theorem bxor_comm : ∀ {m : ℕ} (u v : BUnit m), bxor u v = bxor v u
  | 0, BUnit.real0, BUnit.real0 => rfl
  | _ + 1, BUnit.lower u, BUnit.lower v => by
      show BUnit.lower (bxor u v) = BUnit.lower (bxor v u); rw [bxor_comm u v]
  | _ + 1, BUnit.lower u, BUnit.upper v => by
      show BUnit.upper (bxor u v) = BUnit.upper (bxor v u); rw [bxor_comm u v]
  | _ + 1, BUnit.upper u, BUnit.lower v => by
      show BUnit.upper (bxor u v) = BUnit.upper (bxor v u); rw [bxor_comm u v]
  | _ + 1, BUnit.upper u, BUnit.upper v => by
      show BUnit.lower (bxor u v) = BUnit.lower (bxor v u); rw [bxor_comm u v]

theorem bxor_assoc : ∀ {m : ℕ} (u v w : BUnit m), bxor (bxor u v) w = bxor u (bxor v w)
  | 0, BUnit.real0, BUnit.real0, BUnit.real0 => rfl
  | _ + 1, BUnit.lower u, BUnit.lower v, BUnit.lower w => by
      show BUnit.lower (bxor (bxor u v) w) = BUnit.lower (bxor u (bxor v w))
      rw [bxor_assoc u v w]
  | _ + 1, BUnit.lower u, BUnit.lower v, BUnit.upper w => by
      show BUnit.upper (bxor (bxor u v) w) = BUnit.upper (bxor u (bxor v w))
      rw [bxor_assoc u v w]
  | _ + 1, BUnit.lower u, BUnit.upper v, BUnit.lower w => by
      show BUnit.upper (bxor (bxor u v) w) = BUnit.upper (bxor u (bxor v w))
      rw [bxor_assoc u v w]
  | _ + 1, BUnit.lower u, BUnit.upper v, BUnit.upper w => by
      show BUnit.lower (bxor (bxor u v) w) = BUnit.lower (bxor u (bxor v w))
      rw [bxor_assoc u v w]
  | _ + 1, BUnit.upper u, BUnit.lower v, BUnit.lower w => by
      show BUnit.upper (bxor (bxor u v) w) = BUnit.upper (bxor u (bxor v w))
      rw [bxor_assoc u v w]
  | _ + 1, BUnit.upper u, BUnit.lower v, BUnit.upper w => by
      show BUnit.lower (bxor (bxor u v) w) = BUnit.lower (bxor u (bxor v w))
      rw [bxor_assoc u v w]
  | _ + 1, BUnit.upper u, BUnit.upper v, BUnit.lower w => by
      show BUnit.lower (bxor (bxor u v) w) = BUnit.lower (bxor u (bxor v w))
      rw [bxor_assoc u v w]
  | _ + 1, BUnit.upper u, BUnit.upper v, BUnit.upper w => by
      show BUnit.upper (bxor (bxor u v) w) = BUnit.upper (bxor u (bxor v w))
      rw [bxor_assoc u v w]

theorem bxor_self : ∀ {m : ℕ} (u : BUnit m), bxor u u = bone m
  | 0, BUnit.real0 => rfl
  | _ + 1, BUnit.lower u => by
      show BUnit.lower (bxor u u) = BUnit.lower (bone _); rw [bxor_self u]
  | _ + 1, BUnit.upper u => by
      show BUnit.lower (bxor u u) = BUnit.lower (bone _); rw [bxor_self u]

theorem bxor_bone : ∀ {m : ℕ} (u : BUnit m), bxor u (bone m) = u
  | 0, BUnit.real0 => rfl
  | _ + 1, BUnit.lower u => by
      show BUnit.lower (bxor u (bone _)) = BUnit.lower u; rw [bxor_bone u]
  | _ + 1, BUnit.upper u => by
      show BUnit.upper (bxor u (bone _)) = BUnit.upper u; rw [bxor_bone u]

theorem bone_bxor {m : ℕ} (u : BUnit m) : bxor (bone m) u = u := by
  rw [bxor_comm, bxor_bone]

theorem bxor_bxor_cancel {m : ℕ} (a u : BUnit m) : bxor a (bxor a u) = u := by
  rw [← bxor_assoc, bxor_self, bone_bxor]

theorem bxor_eq_bone_iff {m : ℕ} {a u : BUnit m} : bxor a u = bone m ↔ a = u := by
  constructor
  · intro h
    have := congrArg (bxor a) h
    rw [bxor_bxor_cancel, bxor_bone] at this
    exact this.symm
  · rintro rfl; exact bxor_self a

theorem bxor_eq_left_iff {m : ℕ} {a u : BUnit m} : bxor a u = a ↔ u = bone m := by
  constructor
  · intro h
    have := congrArg (bxor a) h
    rw [bxor_bxor_cancel, bxor_self] at this
    exact this
  · rintro rfl; exact bxor_bone a

theorem bxor_eq_right_iff {m : ℕ} {a u : BUnit m} : bxor a u = u ↔ a = bone m := by
  rw [bxor_comm]; exact bxor_eq_left_iff

theorem bxor_left_inj {m : ℕ} {a u v : BUnit m} (h : bxor a u = bxor a v) : u = v := by
  have := congrArg (bxor a) h
  rwa [bxor_bxor_cancel, bxor_bxor_cancel] at this

/-- The product of two units is, up to sign, the unit of the xor index. -/
theorem beval_mul_same : ∀ {m : ℕ} (u v : BUnit m),
    Same (beval u * beval v) (beval (bxor u v))
  | 0, BUnit.real0, BUnit.real0 => Or.inl (mul_one _)
  | n + 1, BUnit.lower u, BUnit.lower v => by
      show Same (dbl (beval u) (cdZero : CD n) * dbl (beval v) (cdZero : CD n))
        (dbl (beval (bxor u v)) (cdZero : CD n))
      rw [mul_LL]
      exact (beval_mul_same u v).dblL
  | n + 1, BUnit.lower u, BUnit.upper v => by
      show Same (dbl (beval u) (cdZero : CD n) * dbl (cdZero : CD n) (beval v))
        (dbl (cdZero : CD n) (beval (bxor u v)))
      rw [mul_LU]
      exact (((same_conj_beval u).mul_right (beval v)).trans (beval_mul_same u v)).dblU
  | n + 1, BUnit.upper u, BUnit.lower v => by
      show Same (dbl (cdZero : CD n) (beval u) * dbl (beval v) (cdZero : CD n))
        (dbl (cdZero : CD n) (beval (bxor u v)))
      rw [mul_UL, bxor_comm]
      exact (beval_mul_same v u).dblU
  | n + 1, BUnit.upper u, BUnit.upper v => by
      show Same (dbl (cdZero : CD n) (beval u) * dbl (cdZero : CD n) (beval v))
        (dbl (beval (bxor u v)) (cdZero : CD n))
      rw [mul_UU, bxor_comm]
      exact ((((same_conj_beval u).mul_left (beval v)).trans
        (beval_mul_same v u)).neg_left).dblL

/-- Triple products of units: both bracketings land on the same unit up to sign. -/
theorem beval_triple_same {m : ℕ} (u v w : BUnit m) :
    Same ((beval u * beval v) * beval w) (beval u * (beval v * beval w)) := by
  have h1 : Same ((beval u * beval v) * beval w) (beval (bxor (bxor u v) w)) :=
    ((beval_mul_same u v).mul_right (beval w)).trans (beval_mul_same _ w)
  have h2 : Same (beval u * (beval v * beval w)) (beval (bxor u (bxor v w))) :=
    ((beval_mul_same v w).mul_left (beval u)).trans (beval_mul_same u _)
  rw [bxor_assoc] at h1
  exact h1.trans h2.symm

/-- A unit is never its own negative. -/
theorem beval_ne_neg_self {m : ℕ} (u : BUnit m) : beval u ≠ neg (beval u) := by
  intro h
  exact basisUnit_neg_not (beval_basis u) (beval_basis u) h

/-- A unit is never zero. -/
theorem beval_ne_zero {m : ℕ} (u : BUnit m) : beval u ≠ cdZero :=
  basisUnit_ne_zero (beval_basis u)

/-! ## Floor B: the anti-associator count is the kernel dimension -/

/-- The triple (e_a, e_r, e_b) anti-associates. -/
def Anti {m : ℕ} (a b r : BUnit m) : Prop :=
  (beval a * beval r) * beval b = neg (beval a * (beval r * beval b))

open Classical in
/-- The birth count: how many units anti-associate between e_a and e_b. -/
noncomputable def N {m : ℕ} (a b : BUnit m) : ℕ :=
  ∑ r : BUnit m, if Anti a b r then 1 else 0

/-- The index W(e_a,e_b) sends e_r to. -/
def tgt {m : ℕ} (a b r : BUnit m) : BUnit m := bxor a (bxor r b)

theorem tgt_injective {m : ℕ} (a b : BUnit m) : Function.Injective (tgt a b) := by
  intro r s h
  have h1 : bxor r b = bxor s b := bxor_left_inj h
  rw [bxor_comm r b, bxor_comm s b] at h1
  exact bxor_left_inj h1

theorem same_ne_neg {m : ℕ} {t : CD m} (u : BUnit m) (h : Same t (beval u)) :
    t ≠ neg t := by
  intro ht
  rcases h with h | h
  · rw [h] at ht; exact beval_ne_neg_self u ht
  · rw [h, neg_neg] at ht; exact beval_ne_neg_self u ht.symm

theorem right_same {m : ℕ} (a b r : BUnit m) :
    Same (beval a * (beval r * beval b)) (beval (tgt a b r)) :=
  ((beval_mul_same r b).mul_left (beval a)).trans (beval_mul_same a _)

theorem not_anti_iff {m : ℕ} (a b r : BUnit m) :
    ¬ Anti a b r ↔ (beval a * beval r) * beval b = beval a * (beval r * beval b) := by
  constructor
  · intro h
    rcases beval_triple_same a r b with h' | h'
    · exact h'
    · exact absurd h' h
  · intro h hA
    unfold Anti at hA
    rw [h] at hA
    exact same_ne_neg (tgt a b r) (right_same a b r) hA

theorem WA_apply {m : ℕ} (x y a : CD m) : WA x y a = (x * a) * y + x * (a * y) := rfl

theorem WA_beval_of_anti {m : ℕ} {a b r : BUnit m} (h : Anti a b r) :
    WA (beval a) (beval b) (beval r) = cdZero := by
  rw [WA_apply, h, neg_add_self]

theorem WA_beval_of_not_anti {m : ℕ} {a b r : BUnit m} (h : ¬ Anti a b r) :
    WA (beval a) (beval b) (beval r) = (2 : ℝ) • (beval a * (beval r * beval b)) := by
  rw [WA_apply, (not_anti_iff a b r).1 h, two_smul]

/-- Signed-scalar form of `Same`. -/
theorem same_smul {m : ℕ} {t : CD m} (u : BUnit m) (h : Same t (beval u)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ t = ε • beval u := by
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, _root_.one_smul]⟩
  · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]; rfl⟩

theorem coordLm_eq_repr {m : ℕ} (j : BUnit m) (v : CD m) :
    coordLm j v = (bevalBasis m).repr v j := rfl

/-- Off the diagonal, the target coordinate of W(e_i) vanishes. -/
theorem coord_WA_beval_ne {m : ℕ} (a b : BUnit m) {i r₀ : BUnit m} (hne : i ≠ r₀) :
    coordLm (tgt a b r₀) (WA (beval a) (beval b) (beval i)) = 0 := by
  by_cases hA : Anti a b i
  · rw [WA_beval_of_anti hA]
    exact map_zero _
  · rw [WA_beval_of_not_anti hA]
    obtain ⟨ε, -, hε⟩ := same_smul (tgt a b i) (right_same a b i)
    rw [hε, map_smul, map_smul,
      coord_val_ne _ _ (fun h => hne (tgt_injective a b h)),
      _root_.smul_zero, _root_.smul_zero]

/-- On the diagonal, the target coordinate of W(e_r₀) is a nonzero scalar. -/
theorem coord_WA_beval_self {m : ℕ} (a b : BUnit m) {r₀ : BUnit m} (h : ¬ Anti a b r₀) :
    ∃ κ : ℝ, κ ≠ 0 ∧ coordLm (tgt a b r₀) (WA (beval a) (beval b) (beval r₀)) = κ := by
  obtain ⟨ε, hε1, hε⟩ := same_smul (tgt a b r₀) (right_same a b r₀)
  refine ⟨2 * ε, ?_, ?_⟩
  · rcases hε1 with rfl | rfl <;> norm_num
  · rw [WA_beval_of_not_anti h, hε, map_smul, map_smul, coord_apply, if_pos rfl,
      smul_eq_mul, smul_eq_mul, _root_.mul_one]

theorem bevalBasis_coe (m : ℕ) : ⇑(bevalBasis m) = beval := funext (bevalBasis_apply m)

/-- Coordinates of an element of the kernel vanish off the anti-associating set. -/
theorem repr_eq_zero_of_ker {m : ℕ} (a b : BUnit m) {v : CD m}
    (hv : WA (beval a) (beval b) v = 0) {r₀ : BUnit m} (h : ¬ Anti a b r₀) :
    (bevalBasis m).repr v r₀ = 0 := by
  have hsum : v = ∑ i : BUnit m, (bevalBasis m).repr v i • beval i := by
    have h := (bevalBasis m).sum_repr v
    rw [bevalBasis_coe] at h
    exact h.symm
  have hW : coordLm (tgt a b r₀) (WA (beval a) (beval b) v)
      = ∑ i : BUnit m, (bevalBasis m).repr v i
          * coordLm (tgt a b r₀) (WA (beval a) (beval b) (beval i)) := by
    conv_lhs => rw [hsum]
    rw [map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  obtain ⟨κ, hκ, hκeq⟩ := coord_WA_beval_self a b h
  rw [Finset.sum_eq_single r₀ (fun i _ hi => by
      rw [coord_WA_beval_ne a b hi]; exact MulZeroClass.mul_zero _)
    (fun habs => absurd (Finset.mem_univ r₀) habs), hκeq, hv, map_zero] at hW
  exact (mul_eq_zero.1 hW.symm).resolve_right hκ

/-- The kernel of W(e_a,e_b) is spanned by the anti-associating units. -/
theorem ker_WA_eq_span {m : ℕ} (a b : BUnit m) :
    LinearMap.ker (WA (beval a) (beval b))
      = Submodule.span ℝ (beval '' {r | Anti a b r}) := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [← bevalBasis_coe, Module.Basis.mem_span_image]
    intro r hr
    by_contra hA
    exact (Finsupp.mem_support_iff.1 hr) (repr_eq_zero_of_ker a b hv hA)
  · rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    exact WA_beval_of_anti hr

open Classical in
/-- **Monomial kernel lemma**: `dim ker W(e_a,e_b) = N a b`. -/
theorem finrank_ker_WA_eq_N {m : ℕ} (a b : BUnit m) :
    Module.finrank ℝ (LinearMap.ker (WA (beval a) (beval b))) = N a b := by
  rw [ker_WA_eq_span, Set.image_eq_range]
  have hli : LinearIndependent ℝ (fun x : ↥{r | Anti a b r} => beval x.1) :=
    beval_linearIndependent.comp Subtype.val Subtype.val_injective
  rw [finrank_span_eq_card hli, N, ← Finset.card_filter, ← Set.toFinset_card,
    Set.toFinset_setOf]

/-! ## Floor C1: the level-n toolbox and the six key reductions -/

theorem beval_eq_one_iff {m : ℕ} {u : BUnit m} : beval u = (cdOne : CD m) ↔ u = bone m := by
  constructor
  · intro h
    exact beval_inj m u (bone m) (by rw [h, beval_bone])
  · rintro rfl
    exact beval_bone m

theorem conj_beval_of_ne {m : ℕ} {u : BUnit m} (h : u ≠ bone m) :
    conj (beval u) = neg (beval u) := by
  rcases (basisUnit_pack (beval_basis u)).1 with h1 | ⟨h1, -⟩
  · exact absurd (beval_eq_one_iff.1 h1) h
  · exact h1

theorem conj_beval_bone (m : ℕ) : conj (beval (bone m)) = beval (bone m) := by
  rw [beval_bone]; exact conj_one

theorem sq_beval {m : ℕ} {u : BUnit m} (h : u ≠ bone m) :
    beval u * beval u = neg (cdOne : CD m) :=
  basisUnit_sq (beval_basis u) (conj_beval_of_ne h)

/-- Distinct imaginary units anticommute: `e_v e_u = −e_u e_v`. -/
theorem anticomm_beval {m : ℕ} {u v : BUnit m} (hu : u ≠ bone m) (hv : v ≠ bone m)
    (huv : u ≠ v) : beval v * beval u = neg (beval u * beval v) :=
  basisUnit_anticomm (beval_basis u) (beval_basis v) (conj_beval_of_ne hu)
    (conj_beval_of_ne hv) (fun h => huv (beval_inj m u v h))

theorem lart {m : ℕ} (u : BUnit m) (w : CD m) :
    beval u * (beval u * w) = (beval u * beval u) * w :=
  basisUnit_left_art (beval_basis u) w

theorem rart {m : ℕ} (u : BUnit m) (w : CD m) :
    (w * beval u) * beval u = w * (beval u * beval u) :=
  basisUnit_right_art (beval_basis u) w

theorem x_xw {m : ℕ} {a : BUnit m} (ha : a ≠ bone m) (w : CD m) :
    beval a * (beval a * w) = neg w := by
  rw [lart, sq_beval ha, neg_one_mul]

theorem wx_x {m : ℕ} {a : BUnit m} (ha : a ≠ bone m) (w : CD m) :
    (w * beval a) * beval a = neg w := by
  rw [rart, sq_beval ha, mul_neg_one]

theorem y_xy {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m) (hab : a ≠ b) :
    beval b * (beval a * beval b) = beval a := by
  rw [anticomm_beval hb ha (Ne.symm hab), mul_neg, x_xw hb, neg_neg]

theorem xy_x {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m) (hab : a ≠ b) :
    (beval a * beval b) * beval a = beval b := by
  rw [anticomm_beval hb ha (Ne.symm hab), neg_mul, wx_x ha, neg_neg]

theorem x_yx {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m) (hab : a ≠ b) :
    beval a * (beval b * beval a) = beval b := by
  rw [anticomm_beval ha hb hab, mul_neg, x_xw ha, neg_neg]

theorem yx_y {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m) (hab : a ≠ b) :
    (beval b * beval a) * beval b = beval a := by
  rw [anticomm_beval ha hb hab, neg_mul, wx_x hb, neg_neg]

/-- An imaginary unit anticommutes with anything equal, up to sign, to a
distinct imaginary unit. -/
theorem anticomm_same_left {m : ℕ} {b v : BUnit m} (hb : b ≠ bone m) (hv : v ≠ bone m)
    (hbv : b ≠ v) {t : CD m} (ht : Same t (beval v)) :
    beval b * t = neg (t * beval b) := by
  rcases ht with rfl | rfl
  · exact anticomm_beval hv hb (Ne.symm hbv)
  · rw [mul_neg, neg_mul, anticomm_beval hv hb (Ne.symm hbv)]

theorem anticomm_same_right {m : ℕ} {b v : BUnit m} (hb : b ≠ bone m) (hv : v ≠ bone m)
    (hbv : b ≠ v) {t : CD m} (ht : Same t (beval v)) :
    t * beval b = neg (beval b * t) := by
  rw [anticomm_same_left hb hv hbv ht, neg_neg]

theorem neg_eq_neg_iff {m : ℕ} {A B : CD m} : neg A = neg B ↔ A = B :=
  ⟨neg_inj, fun h => by rw [h]⟩

theorem neg_eq_comm' {m : ℕ} {A B : CD m} : neg A = B ↔ A = neg B := by
  constructor
  · intro h; rw [← h, neg_neg]
  · intro h; rw [h, neg_neg]

theorem dblL_eq_iff {n : ℕ} {p r : CD n} :
    dbl p (cdZero : CD n) = dbl r (cdZero : CD n) ↔ p = r := by
  constructor
  · intro h
    exact congrArg Prod.fst (congrArg cdUnpair h)
  · intro h; rw [h]

theorem dblU_eq_iff {n : ℕ} {p r : CD n} :
    dbl (cdZero : CD n) p = dbl (cdZero : CD n) r ↔ p = r := by
  constructor
  · intro h
    exact congrArg Prod.snd (congrArg cdUnpair h)
  · intro h; rw [h]

theorem neg_dblL {n : ℕ} (p : CD n) :
    neg (dbl p (cdZero : CD n)) = dbl (neg p) (cdZero : CD n) := by
  rw [neg_dbl, neg_zero]

theorem neg_dblU {n : ℕ} (p : CD n) :
    neg (dbl (cdZero : CD n) p) = dbl (cdZero : CD n) (neg p) := by
  rw [neg_dbl, neg_zero]

/-- LL, lower slot: anti iff anti one level down. -/
theorem key_LL_lower {n : ℕ} (a b u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.lower b) (BUnit.lower u) ↔ Anti a b u := by
  unfold Anti
  show dbl (beval a) (cdZero : CD n) * dbl (beval u) cdZero * dbl (beval b) cdZero
      = neg (dbl (beval a) cdZero * (dbl (beval u) cdZero * dbl (beval b) cdZero)) ↔ _
  simp only [mul_LL]
  rw [neg_dblL]
  exact dblL_eq_iff

/-- LL, upper slot. -/
theorem key_LL_upper {n : ℕ} (a b u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.lower b) (BUnit.upper u)
      ↔ beval b * (conj (beval a) * beval u) = neg (conj (beval a) * (beval b * beval u)) := by
  unfold Anti
  show dbl (beval a) (cdZero : CD n) * dbl cdZero (beval u) * dbl (beval b) cdZero
      = neg (dbl (beval a) cdZero * (dbl cdZero (beval u) * dbl (beval b) cdZero)) ↔ _
  simp only [mul_LU, mul_UL]
  rw [neg_dblU]
  exact dblU_eq_iff

/-- LU, lower slot. -/
theorem key_LU_lower {n : ℕ} (a b u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.upper b) (BUnit.lower u)
      ↔ (conj (beval u) * conj (beval a)) * beval b
          = neg (conj (beval a) * (conj (beval u) * beval b)) := by
  unfold Anti
  show dbl (beval a) (cdZero : CD n) * dbl (beval u) cdZero * dbl cdZero (beval b)
      = neg (dbl (beval a) cdZero * (dbl (beval u) cdZero * dbl cdZero (beval b))) ↔ _
  simp only [mul_LL, mul_LU]
  rw [neg_dblU, conj_mul]
  exact dblU_eq_iff

/-- LU, upper slot. -/
theorem key_LU_upper {n : ℕ} (a b u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.upper b) (BUnit.upper u)
      ↔ beval b * (conj (beval u) * beval a)
          = neg (beval a * (beval b * conj (beval u))) := by
  unfold Anti
  show dbl (beval a) (cdZero : CD n) * dbl cdZero (beval u) * dbl cdZero (beval b)
      = neg (dbl (beval a) cdZero * (dbl cdZero (beval u) * dbl cdZero (beval b))) ↔ _
  simp only [mul_LU, mul_UU, mul_LL]
  rw [neg_dblL, conj_mul, conj_conj, mul_neg, neg_neg]
  exact dblL_eq_iff.trans neg_eq_comm'

/-- UU, lower slot. -/
theorem key_UU_lower {n : ℕ} (a b u : BUnit n) :
    Anti (BUnit.upper a) (BUnit.upper b) (BUnit.lower u)
      ↔ beval b * (conj (beval a) * conj (beval u))
          = neg ((conj (beval u) * beval b) * conj (beval a)) := by
  unfold Anti
  show dbl (cdZero : CD n) (beval a) * dbl (beval u) cdZero * dbl cdZero (beval b)
      = neg (dbl cdZero (beval a) * (dbl (beval u) cdZero * dbl cdZero (beval b))) ↔ _
  simp only [mul_UL, mul_UU, mul_LU]
  rw [neg_dblL, conj_mul, neg_neg]
  exact dblL_eq_iff.trans neg_eq_comm'

/-- UU, upper slot. -/
theorem key_UU_upper {n : ℕ} (a b u : BUnit n) :
    Anti (BUnit.upper a) (BUnit.upper b) (BUnit.upper u)
      ↔ (beval a * conj (beval u)) * beval b
          = neg ((beval b * conj (beval u)) * beval a) := by
  unfold Anti
  show dbl (cdZero : CD n) (beval a) * dbl cdZero (beval u) * dbl cdZero (beval b)
      = neg (dbl cdZero (beval a) * (dbl cdZero (beval u) * dbl cdZero (beval b))) ↔ _
  simp only [mul_UU, mul_LU, mul_UL]
  rw [neg_dblU, conj_neg, conj_mul, conj_conj, neg_mul, neg_mul, neg_neg]
  exact dblU_eq_iff.trans neg_eq_comm'

/-! ## Floor C2: the quaternion index set and the twelve half-classifications -/

/-- The quaternion index set H⟨a,b⟩ = {1, a, b, ab}. -/
def Hset {m : ℕ} (a b : BUnit m) : Finset (BUnit m) := {bone m, a, b, bxor a b}

theorem mem_Hset {m : ℕ} {a b u : BUnit m} :
    u ∈ Hset a b ↔ u = bone m ∨ u = a ∨ u = b ∨ u = bxor a b := by
  simp only [Hset, Finset.mem_insert, Finset.mem_singleton]

theorem not_mem_Hset {m : ℕ} {a b u : BUnit m} (hu : u ∉ Hset a b) :
    u ≠ bone m ∧ u ≠ a ∧ u ≠ b ∧ u ≠ bxor a b := by
  simp only [mem_Hset, not_or] at hu
  exact hu

theorem mem_Hset_of {m : ℕ} {a b u : BUnit m} (h1 : u ≠ bone m) (h2 : u ≠ a) (h3 : u ≠ b)
    (h4 : u ≠ bxor a b) : u ∉ Hset a b := by
  intro h
  rcases mem_Hset.1 h with h | h | h | h
  exacts [h1 h, h2 h, h3 h, h4 h]

theorem bxor_au_ne_bone {m : ℕ} {a u : BUnit m} (h : u ≠ a) : bxor a u ≠ bone m :=
  fun h' => h (bxor_eq_bone_iff.1 h').symm

theorem bxor_au_ne_b {m : ℕ} {a b u : BUnit m} (h : u ≠ bxor a b) : bxor a u ≠ b :=
  fun h' => h (by rw [← h', bxor_bxor_cancel])

theorem bxor_ub_ne_bone {m : ℕ} {b u : BUnit m} (h : u ≠ b) : bxor u b ≠ bone m :=
  fun h' => h (bxor_eq_bone_iff.1 h')

theorem bxor_ub_ne_a {m : ℕ} {a b u : BUnit m} (h : u ≠ bxor a b) : bxor u b ≠ a :=
  fun h' => h (by rw [← h', bxor_assoc, bxor_self, bxor_bone])

theorem bxor_bu_ne_a {m : ℕ} {a b u : BUnit m} (h : u ≠ bxor a b) : bxor b u ≠ a :=
  fun h' => h (by rw [← h', bxor_comm (bxor b u) b, ← bxor_assoc, bxor_self, bone_bxor])

theorem bone_ne_bxor {m : ℕ} {a b : BUnit m} (hab : a ≠ b) : bone m ≠ bxor a b :=
  fun h => hab (bxor_eq_bone_iff.1 h.symm)

theorem a_ne_bxor {m : ℕ} {a b : BUnit m} (hb : b ≠ bone m) : a ≠ bxor a b :=
  fun h => hb (bxor_eq_left_iff.1 h.symm)

theorem b_ne_bxor {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) : b ≠ bxor a b :=
  fun h => ha (bxor_eq_right_iff.1 h.symm)

/-- For fresh u, y anticommutes with x·u. -/
theorem y_xu_anti {m : ℕ} {a b u : BUnit m} (hb : b ≠ bone m) (hu : u ∉ Hset a b) :
    beval b * (beval a * beval u) = neg ((beval a * beval u) * beval b) := by
  obtain ⟨-, hua, -, huw⟩ := not_mem_Hset hu
  exact anticomm_same_left hb (bxor_au_ne_bone hua) (Ne.symm (bxor_au_ne_b huw))
    (beval_mul_same a u)

/-- The H-units associate: no anti-associator inside the quaternion. -/
theorem not_anti_of_mem_Hset {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m)
    (hab : a ≠ b) {u : BUnit m} (hu : u ∈ Hset a b) : ¬ Anti a b u := by
  rw [not_anti_iff]
  rcases mem_Hset.1 hu with rfl | rfl | rfl | rfl
  · rw [beval_bone, mul_one, one_mul]
  · rw [sq_beval ha, neg_one_mul, x_xw ha]
  · rw [wx_x hb, sq_beval hb, mul_neg_one]
  · rcases beval_mul_same a b with hz | hz
    · rw [← hz, x_xw ha, neg_mul, wx_x hb, mul_neg, sq_beval hb, sq_beval ha]
    · have hz' : beval (bxor a b) = neg (beval a * beval b) := by rw [hz, neg_neg]
      rw [hz', mul_neg, x_xw ha, neg_neg, neg_mul, wx_x hb, neg_neg, sq_beval hb, sq_beval ha]

/-- (1) LL, upper slot: H plus the anti-associating fresh units. -/
theorem class_LL_upper {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n)
    (hab : a ≠ b) (u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.lower b) (BUnit.upper u)
      ↔ (u ∈ Hset a b ∨ (u ∉ Hset a b ∧ Anti a b u)) := by
  rw [key_LL_upper, conj_beval_of_ne ha, neg_mul, mul_neg, neg_mul, neg_neg]
  by_cases hu : u ∈ Hset a b
  · refine iff_of_true ?_ (Or.inl hu)
    rcases mem_Hset.1 hu with rfl | rfl | rfl | rfl
    · rw [beval_bone, mul_one, mul_one, anticomm_beval ha hb hab, neg_neg]
    · rw [sq_beval ha, mul_neg_one, neg_neg, x_yx ha hb hab]
    · rw [y_xy ha hb hab, sq_beval hb, mul_neg_one]
    · rcases beval_mul_same a b with hz | hz
      · rw [← hz, x_xw ha, mul_neg, sq_beval hb, neg_neg, y_xy ha hb hab, sq_beval ha]
      · have hz' : beval (bxor a b) = neg (beval a * beval b) := by rw [hz, neg_neg]
        rw [hz', mul_neg, x_xw ha, neg_neg, sq_beval hb, mul_neg, y_xy ha hb hab, mul_neg,
          sq_beval ha]
  · obtain ⟨hu1, -, hub, -⟩ := not_mem_Hset hu
    rw [y_xu_anti hb hu, neg_neg, anticomm_beval hu1 hb hub, mul_neg]
    constructor
    · intro h; exact Or.inr ⟨hu, h⟩
    · rintro (h | ⟨-, h⟩)
      · exact absurd h hu
      · exact h

/-- (2) LU, lower slot: {b, ab} plus the associating fresh units. -/
theorem class_LU_lower {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n)
    (hab : a ≠ b) (u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.upper b) (BUnit.lower u)
      ↔ ((u = b ∨ u = bxor a b) ∨ (u ∉ Hset a b ∧ ¬ Anti a b u)) := by
  rw [key_LU_lower, conj_beval_of_ne ha, mul_neg, neg_mul, neg_mul, neg_neg]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, one_mul, one_mul]
    refine iff_of_false (fun h => same_ne_neg (bxor a b) (beval_mul_same a b) h.symm) ?_
    rintro ((h | h) | ⟨h, -⟩)
    · exact hb h.symm
    · exact bone_ne_bxor hab h
    · exact h (mem_Hset.2 (Or.inl rfl))
  · rw [conj_beval_of_ne hu1, neg_mul, neg_mul, neg_neg, neg_mul, mul_neg]
    by_cases hua : u = a
    · rw [hua, sq_beval ha, neg_one_mul, x_xw ha, neg_neg]
      refine iff_of_false (fun h => beval_ne_neg_self b h.symm) ?_
      rintro ((h | h) | ⟨h, -⟩)
      · exact hab h
      · exact a_ne_bxor hb h
      · exact h (mem_Hset.2 (Or.inr (Or.inl rfl)))
    · by_cases hub : u = b
      · rw [hub, yx_y ha hb hab, sq_beval hb, mul_neg_one, neg_neg]
        exact iff_of_true rfl (Or.inl (Or.inl rfl))
      · by_cases huw : u = bxor a b
        · rw [huw]
          refine iff_of_true ?_ (Or.inl (Or.inr rfl))
          rcases beval_mul_same a b with hz | hz
          · rw [← hz, xy_x ha hb hab, wx_x hb, mul_neg, neg_neg, sq_beval hb, sq_beval ha]
          · have hz' : beval (bxor a b) = neg (beval a * beval b) := by rw [hz, neg_neg]
            rw [hz', neg_mul, neg_mul, neg_mul, xy_x ha hb hab, wx_x hb, neg_neg, sq_beval hb,
              sq_beval ha]
        · have hu : u ∉ Hset a b := mem_Hset_of hu1 hua hub huw
          rw [anticomm_beval ha hu1 (Ne.symm hua), neg_mul, neg_eq_neg_iff, ← not_anti_iff]
          constructor
          · intro h; exact Or.inr ⟨hu, h⟩
          · rintro ((h | h) | ⟨-, h⟩)
            · exact absurd h hub
            · exact absurd h huw
            · exact h

/-- (3) LU, upper slot: {1, a} plus the associating fresh units. -/
theorem class_LU_upper {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n)
    (hab : a ≠ b) (u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.upper b) (BUnit.upper u)
      ↔ ((u = bone n ∨ u = a) ∨ (u ∉ Hset a b ∧ ¬ Anti a b u)) := by
  rw [key_LU_upper]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, one_mul, mul_one]
    exact iff_of_true (anticomm_beval ha hb hab) (Or.inl (Or.inl rfl))
  · rw [conj_beval_of_ne hu1, neg_mul, mul_neg, mul_neg, mul_neg, neg_neg]
    by_cases hua : u = a
    · rw [hua, sq_beval ha, mul_neg_one, neg_neg, x_yx ha hb hab]
      exact iff_of_true rfl (Or.inl (Or.inr rfl))
    · by_cases hub : u = b
      · rw [hub, x_xw hb, neg_neg, sq_beval hb, mul_neg_one]
        refine iff_of_false (beval_ne_neg_self a) ?_
        rintro ((h | h) | ⟨h, -⟩)
        · exact hb h
        · exact hab h.symm
        · exact h (mem_Hset.2 (Or.inr (Or.inr (Or.inl rfl))))
      · by_cases huw : u = bxor a b
        · rw [huw]
          refine iff_of_false ?_ ?_
          · rcases beval_mul_same a b with hz | hz
            · rw [← hz, xy_x ha hb hab, y_xy ha hb hab, sq_beval hb, sq_beval ha, neg_neg]
              exact cdOne_ne_neg_one
            · have hz' : beval (bxor a b) = neg (beval a * beval b) := by rw [hz, neg_neg]
              rw [hz', neg_mul, mul_neg, xy_x ha hb hab, mul_neg, y_xy ha hb hab, mul_neg,
                sq_beval hb, sq_beval ha, neg_neg, neg_neg]
              exact fun h => cdOne_ne_neg_one h.symm
          · rintro ((h | h) | ⟨h, -⟩)
            · exact bone_ne_bxor hab h.symm
            · exact a_ne_bxor hb h.symm
            · exact h (mem_Hset.2 (Or.inr (Or.inr (Or.inr rfl))))
        · have hu : u ∉ Hset a b := mem_Hset_of hu1 hua hub huw
          rw [anticomm_beval ha hu1 (Ne.symm hua), mul_neg, neg_neg, y_xu_anti hb hu,
            anticomm_beval hu1 hb hub, mul_neg, neg_eq_neg_iff, ← not_anti_iff]
          constructor
          · intro h; exact Or.inr ⟨hu, h⟩
          · rintro ((h | h) | ⟨-, h⟩)
            · exact absurd h hu1
            · exact absurd h hua
            · exact h

/-- (4) LU with b = 1, lower slot: everything but 1 and a. -/
theorem class_LU_bone_lower {n : ℕ} {a : BUnit n} (ha : a ≠ bone n) (u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.upper (bone n)) (BUnit.lower u) ↔ (u ≠ bone n ∧ u ≠ a) := by
  rw [key_LU_lower, beval_bone, mul_one, mul_one, conj_beval_of_ne ha, mul_neg, neg_mul,
    neg_neg]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, one_mul, mul_one]
    exact iff_of_false (fun h => beval_ne_neg_self a h.symm) (fun h => h.1 rfl)
  · rw [conj_beval_of_ne hu1, neg_mul, neg_neg, mul_neg]
    by_cases hua : u = a
    · rw [hua, sq_beval ha, neg_neg]
      exact iff_of_false (fun h => cdOne_ne_neg_one h.symm) (fun h => h.2 rfl)
    · exact iff_of_true (anticomm_beval ha hu1 (Ne.symm hua)) ⟨hu1, hua⟩

/-- (5) LU with b = 1, upper slot. -/
theorem class_LU_bone_upper {n : ℕ} {a : BUnit n} (ha : a ≠ bone n) (u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.upper (bone n)) (BUnit.upper u) ↔ (u ≠ bone n ∧ u ≠ a) := by
  rw [key_LU_upper, beval_bone, one_mul, one_mul]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, one_mul, mul_one]
    exact iff_of_false (beval_ne_neg_self a) (fun h => h.1 rfl)
  · rw [conj_beval_of_ne hu1, neg_mul, mul_neg, neg_neg]
    by_cases hua : u = a
    · rw [hua, sq_beval ha, neg_neg]
      exact iff_of_false cdOne_ne_neg_one (fun h => h.2 rfl)
    · exact iff_of_true (by rw [anticomm_beval ha hu1 (Ne.symm hua), neg_neg]) ⟨hu1, hua⟩

/-- (6) LU with b = a, lower slot. -/
theorem class_LU_self_lower {n : ℕ} {a : BUnit n} (ha : a ≠ bone n) (u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.upper a) (BUnit.lower u) ↔ (u ≠ bone n ∧ u ≠ a) := by
  rw [key_LU_lower, conj_beval_of_ne ha, mul_neg, neg_mul, neg_mul, neg_neg, wx_x ha, neg_neg]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, one_mul, sq_beval ha]
    exact iff_of_false cdOne_ne_neg_one (fun h => h.1 rfl)
  · rw [conj_beval_of_ne hu1, neg_mul, mul_neg, neg_eq_neg_iff]
    by_cases hua : u = a
    · rw [hua, x_xw ha]
      exact iff_of_false (beval_ne_neg_self a) (fun h => h.2 rfl)
    · rw [anticomm_beval ha hu1 (Ne.symm hua), mul_neg, x_xw ha, neg_neg]
      exact iff_of_true rfl ⟨hu1, hua⟩

/-- (7) LU with b = a, upper slot. -/
theorem class_LU_self_upper {n : ℕ} {a : BUnit n} (ha : a ≠ bone n) (u : BUnit n) :
    Anti (BUnit.lower a) (BUnit.upper a) (BUnit.upper u) ↔ (u ≠ bone n ∧ u ≠ a) := by
  rw [key_LU_upper, x_xw ha, neg_neg]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, one_mul, sq_beval ha]
    exact iff_of_false (fun h => cdOne_ne_neg_one h.symm) (fun h => h.1 rfl)
  · rw [conj_beval_of_ne hu1, neg_mul, mul_neg, neg_eq_neg_iff]
    by_cases hua : u = a
    · rw [hua, x_xw ha]
      exact iff_of_false (fun h => beval_ne_neg_self a h.symm) (fun h => h.2 rfl)
    · rw [anticomm_beval ha hu1 (Ne.symm hua), mul_neg, x_xw ha, neg_neg]
      exact iff_of_true rfl ⟨hu1, hua⟩

/-- (8) UU, lower slot: {a, b} plus the anti-associating fresh units. -/
theorem class_UU_lower {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n)
    (hab : a ≠ b) (u : BUnit n) :
    Anti (BUnit.upper a) (BUnit.upper b) (BUnit.lower u)
      ↔ ((u = a ∨ u = b) ∨ (u ∉ Hset a b ∧ Anti a b u)) := by
  rw [key_UU_lower, conj_beval_of_ne ha, neg_mul, mul_neg, mul_neg, neg_neg]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, mul_one, one_mul]
    refine iff_of_false (fun h => same_ne_neg (bxor b a) (beval_mul_same b a) h.symm) ?_
    rintro ((h | h) | ⟨h, -⟩)
    · exact ha h.symm
    · exact hb h.symm
    · exact h (mem_Hset.2 (Or.inl rfl))
  · rw [conj_beval_of_ne hu1, mul_neg, mul_neg, neg_neg, neg_mul, neg_mul]
    by_cases hua : u = a
    · rw [hua, sq_beval ha, mul_neg_one, xy_x ha hb hab]
      exact iff_of_true rfl (Or.inl (Or.inl rfl))
    · by_cases hub : u = b
      · rw [hub, y_xy ha hb hab, sq_beval hb, neg_one_mul, neg_neg]
        exact iff_of_true rfl (Or.inl (Or.inr rfl))
      · by_cases huw : u = bxor a b
        · rw [huw]
          refine iff_of_false ?_ ?_
          · rcases beval_mul_same a b with hz | hz
            · rw [← hz, x_xw ha, mul_neg, sq_beval hb, wx_x hb, neg_mul, sq_beval ha, neg_neg]
              exact cdOne_ne_neg_one
            · have hz' : beval (bxor a b) = neg (beval a * beval b) := by rw [hz, neg_neg]
              rw [hz', mul_neg, mul_neg, x_xw ha, mul_neg, neg_mul, neg_mul, wx_x hb, neg_mul,
                sq_beval hb, sq_beval ha, neg_neg, neg_neg]
              exact fun h => cdOne_ne_neg_one h.symm
          · rintro ((h | h) | ⟨h, -⟩)
            · exact a_ne_bxor hb h.symm
            · exact b_ne_bxor ha h.symm
            · exact h (mem_Hset.2 (Or.inr (Or.inr (Or.inr rfl))))
        · have hu : u ∉ Hset a b := mem_Hset_of hu1 hua hub huw
          rw [y_xu_anti hb hu,
            anticomm_same_right ha (bxor_ub_ne_bone hub) (Ne.symm (bxor_ub_ne_a huw))
              (beval_mul_same u b), neg_neg, neg_eq_comm']
          constructor
          · intro h; exact Or.inr ⟨hu, h⟩
          · rintro ((h | h) | ⟨-, h⟩)
            · exact absurd h hua
            · exact absurd h hub
            · exact h

/-- (9) UU, upper slot: {1, ab} plus the anti-associating fresh units. -/
theorem class_UU_upper {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n)
    (hab : a ≠ b) (u : BUnit n) :
    Anti (BUnit.upper a) (BUnit.upper b) (BUnit.upper u)
      ↔ ((u = bone n ∨ u = bxor a b) ∨ (u ∉ Hset a b ∧ Anti a b u)) := by
  rw [key_UU_upper]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, mul_one, mul_one]
    exact iff_of_true (by rw [anticomm_beval ha hb hab, neg_neg]) (Or.inl (Or.inl rfl))
  · rw [conj_beval_of_ne hu1, mul_neg, mul_neg, neg_mul, neg_mul, neg_neg]
    by_cases hua : u = a
    · rw [hua, sq_beval ha, neg_one_mul, neg_neg, wx_x ha]
      refine iff_of_false (beval_ne_neg_self b) ?_
      rintro ((h | h) | ⟨h, -⟩)
      · exact ha h
      · exact a_ne_bxor hb h
      · exact h (mem_Hset.2 (Or.inr (Or.inl rfl)))
    · by_cases hub : u = b
      · rw [hub, wx_x hb, neg_neg, sq_beval hb, neg_one_mul]
        refine iff_of_false (beval_ne_neg_self a) ?_
        rintro ((h | h) | ⟨h, -⟩)
        · exact hb h
        · exact b_ne_bxor ha h
        · exact h (mem_Hset.2 (Or.inr (Or.inr (Or.inl rfl))))
      · by_cases huw : u = bxor a b
        · rw [huw]
          refine iff_of_true ?_ (Or.inl (Or.inr rfl))
          rcases beval_mul_same a b with hz | hz
          · rw [← hz, x_xw ha, neg_mul, y_xy ha hb hab, sq_beval hb, sq_beval ha, neg_neg]
          · have hz' : beval (bxor a b) = neg (beval a * beval b) := by rw [hz, neg_neg]
            rw [hz', mul_neg, mul_neg, x_xw ha, neg_mul, neg_mul, neg_mul, y_xy ha hb hab,
              sq_beval hb, sq_beval ha, neg_neg]
        · have hu : u ∉ Hset a b := mem_Hset_of hu1 hua hub huw
          rw [anticomm_same_right ha (bxor_au_ne_bone hub) (Ne.symm (bxor_bu_ne_a huw))
              (beval_mul_same b u), anticomm_beval hu1 hb hub, mul_neg, neg_neg, neg_eq_comm']
          constructor
          · intro h; exact Or.inr ⟨hu, h⟩
          · rintro ((h | h) | ⟨-, h⟩)
            · exact absurd h hu1
            · exact absurd h huw
            · exact h

/-- (10) UU with a = 1, lower slot: everything but 1 and b. -/
theorem class_UU_bone_lower {n : ℕ} {b : BUnit n} (hb : b ≠ bone n) (u : BUnit n) :
    Anti (BUnit.upper (bone n)) (BUnit.upper b) (BUnit.lower u) ↔ (u ≠ bone n ∧ u ≠ b) := by
  rw [key_UU_lower, conj_beval_bone, beval_bone, one_mul, mul_one]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, mul_one, one_mul]
    exact iff_of_false (beval_ne_neg_self b) (fun h => h.1 rfl)
  · rw [conj_beval_of_ne hu1, mul_neg, neg_mul, neg_neg, neg_eq_comm']
    by_cases hub : u = b
    · rw [hub, sq_beval hb, neg_neg]
      exact iff_of_false (fun h => cdOne_ne_neg_one h.symm) (fun h => h.2 rfl)
    · exact iff_of_true (anticomm_beval hu1 hb hub) ⟨hu1, hub⟩

/-- (11) UU with a = 1, upper slot. -/
theorem class_UU_bone_upper {n : ℕ} {b : BUnit n} (hb : b ≠ bone n) (u : BUnit n) :
    Anti (BUnit.upper (bone n)) (BUnit.upper b) (BUnit.upper u) ↔ (u ≠ bone n ∧ u ≠ b) := by
  rw [key_UU_upper, beval_bone, one_mul, mul_one]
  by_cases hu1 : u = bone n
  · subst hu1
    rw [conj_beval_bone, beval_bone, one_mul, mul_one]
    exact iff_of_false (beval_ne_neg_self b) (fun h => h.1 rfl)
  · rw [conj_beval_of_ne hu1, neg_mul, mul_neg, neg_neg, neg_eq_comm']
    by_cases hub : u = b
    · rw [hub, sq_beval hb, neg_neg]
      exact iff_of_false (fun h => cdOne_ne_neg_one h.symm) (fun h => h.2 rfl)
    · exact iff_of_true (anticomm_beval hb hu1 (Ne.symm hub)) ⟨hu1, hub⟩

/-! ## Floor C3: counting, the six recursions, and the birth function -/

open Classical

theorem sum_succ_split {n : ℕ} (g : BUnit (n + 1) → ℕ) :
    ∑ i, g i = (∑ u : BUnit n, g (BUnit.lower u)) + ∑ u : BUnit n, g (BUnit.upper u) := by
  calc ∑ i, g i = ∑ s : BUnit n ⊕ BUnit n, g ((bUnitSuccEquiv n).symm s) :=
        Fintype.sum_equiv (bUnitSuccEquiv n) _ _ (fun j => by cases j <;> rfl)
    _ = _ := Fintype.sum_sum_type _

theorem N_def {m : ℕ} (a b : BUnit m) : N a b = ∑ r : BUnit m, if Anti a b r then 1 else 0 :=
  rfl

theorem N_succ {n : ℕ} (A B : BUnit (n + 1)) :
    N A B = (∑ u : BUnit n, if Anti A B (BUnit.lower u) then 1 else 0)
          + ∑ u : BUnit n, if Anti A B (BUnit.upper u) then 1 else 0 :=
  sum_succ_split _

theorem sum_ite_congr {n : ℕ} {P Q : BUnit n → Prop} (h : ∀ u, P u ↔ Q u) :
    (∑ u, if P u then 1 else 0) = ∑ u, if Q u then (1 : ℕ) else 0 :=
  Finset.sum_congr rfl (fun u _ => if_congr (h u) rfl rfl)

theorem Hset_card {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n) (hab : a ≠ b) :
    (Hset a b).card = 4 := by
  have h1 : bone n ∉ ({a, b, bxor a b} : Finset (BUnit n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha, Ne.symm hb, bone_ne_bxor hab⟩
  have h2 : a ∉ ({b, bxor a b} : Finset (BUnit n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, a_ne_bxor hb⟩
  rw [Hset, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_pair (b_ne_bxor ha)]

theorem four_le_pow {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n) (hab : a ≠ b) :
    4 ≤ 2 ^ n := by
  have := Finset.card_le_univ (Hset a b)
  rwa [Hset_card ha hb hab, bUnit_card] at this

theorem sum_split_Hset {n : ℕ} (a b : BUnit n) (f : BUnit n → ℕ) :
    ∑ u, f u = ∑ u ∈ Hset a b, f u + ∑ u ∈ Finset.univ \ Hset a b, f u := by
  rw [← Finset.sum_sdiff (Finset.subset_univ (Hset a b)), Nat.add_comm]

theorem N_fresh {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n) (hab : a ≠ b) :
    N a b = ∑ u ∈ Finset.univ \ Hset a b, if Anti a b u then 1 else 0 := by
  rw [N_def, sum_split_Hset a b,
    Finset.sum_eq_zero (fun u hu => if_neg (not_anti_of_mem_Hset ha hb hab hu)), Nat.zero_add]

theorem mem_pair_iff {n : ℕ} {u b c : BUnit n} :
    u ∈ ({b, c} : Finset (BUnit n)) ↔ (u = b ∨ u = c) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem sum_Hset_eq_card {n : ℕ} {a b : BUnit n} (P : BUnit n → Prop) (S : Finset (BUnit n))
    (hS : S ⊆ Hset a b) (hP : ∀ u, u ∈ Hset a b → (P u ↔ u ∈ S)) :
    ∑ u ∈ Hset a b, (if P u then 1 else 0) = S.card := by
  rw [Finset.sum_congr rfl (fun u hu => if_congr (hP u hu) rfl rfl),
    ← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]

/-- Count of a classification whose fresh part is `Anti`. -/
theorem count_anti {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n) (hab : a ≠ b)
    (P : BUnit n → Prop) (S : Finset (BUnit n)) (hS : S ⊆ Hset a b)
    (hP : ∀ u, P u ↔ (u ∈ S ∨ (u ∉ Hset a b ∧ Anti a b u))) :
    (∑ u, if P u then 1 else 0) = S.card + N a b := by
  rw [sum_split_Hset a b, N_fresh ha hb hab]
  congr 1
  · exact sum_Hset_eq_card P S hS (fun u hu =>
      ⟨fun h => ((hP u).1 h).resolve_right (fun h' => h'.1 hu), fun h => (hP u).2 (Or.inl h)⟩)
  · refine Finset.sum_congr rfl (fun u hu => if_congr ?_ rfl rfl)
    have hu' : u ∉ Hset a b := (Finset.mem_sdiff.1 hu).2
    exact ⟨fun h => (((hP u).1 h).resolve_left (fun hs => hu' (hS hs))).2,
      fun h => (hP u).2 (Or.inr ⟨hu', h⟩)⟩

/-- Count of a classification whose fresh part is `¬ Anti`. -/
theorem count_not_anti {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n)
    (hab : a ≠ b) (P : BUnit n → Prop) (S : Finset (BUnit n)) (hS : S ⊆ Hset a b)
    (hP : ∀ u, P u ↔ (u ∈ S ∨ (u ∉ Hset a b ∧ ¬ Anti a b u))) :
    (∑ u, if P u then 1 else 0) + N a b + 4 = S.card + 2 ^ n := by
  have hcard : (Finset.univ \ Hset a b).card + 4 = 2 ^ n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, bUnit_card,
      Hset_card ha hb hab]
    exact Nat.sub_add_cancel (four_le_pow ha hb hab)
  have hsplit : ∑ u ∈ Finset.univ \ Hset a b,
      ((if ¬ Anti a b u then 1 else 0) + if Anti a b u then 1 else 0)
        = (Finset.univ \ Hset a b).card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl (fun u _ => by by_cases h : Anti a b u <;> simp [h])
  rw [Finset.sum_add_distrib] at hsplit
  have hH : ∑ u ∈ Hset a b, (if P u then 1 else 0) = S.card :=
    sum_Hset_eq_card P S hS (fun u hu =>
      ⟨fun h => ((hP u).1 h).resolve_right (fun h' => h'.1 hu), fun h => (hP u).2 (Or.inl h)⟩)
  have hF : ∑ u ∈ Finset.univ \ Hset a b, (if P u then 1 else 0)
      = ∑ u ∈ Finset.univ \ Hset a b, (if ¬ Anti a b u then 1 else 0) := by
    refine Finset.sum_congr rfl (fun u hu => if_congr ?_ rfl rfl)
    have hu' : u ∉ Hset a b := (Finset.mem_sdiff.1 hu).2
    exact ⟨fun h => (((hP u).1 h).resolve_left (fun hs => hu' (hS hs))).2,
      fun h => (hP u).2 (Or.inr ⟨hu', h⟩)⟩
  have hN := N_fresh ha hb hab
  rw [sum_split_Hset a b, hH, hF]
  omega

/-- Count of the classification `u ≠ 1 ∧ u ≠ a`. -/
theorem count_two {n : ℕ} {a : BUnit n} (ha : a ≠ bone n) (P : BUnit n → Prop)
    (hP : ∀ u, P u ↔ (u ≠ bone n ∧ u ≠ a)) :
    (∑ u, if P u then 1 else 0) + 2 = 2 ^ n := by
  have h2 : 2 ≤ 2 ^ n := by
    have := Finset.card_le_univ ({bone n, a} : Finset (BUnit n))
    rwa [Finset.card_pair (Ne.symm ha), bUnit_card] at this
  rw [← Finset.sum_sdiff (Finset.subset_univ ({bone n, a} : Finset (BUnit n)))]
  have h0 : ∑ u ∈ ({bone n, a} : Finset (BUnit n)), (if P u then 1 else 0) = 0 :=
    Finset.sum_eq_zero (fun u hu => if_neg (fun hp => by
      rcases mem_pair_iff.1 hu with rfl | rfl
      · exact ((hP _).1 hp).1 rfl
      · exact ((hP _).1 hp).2 rfl))
  have h1 : ∑ u ∈ Finset.univ \ ({bone n, a} : Finset (BUnit n)), (if P u then 1 else 0)
      = (Finset.univ \ ({bone n, a} : Finset (BUnit n))).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl (fun u hu => if_pos ((hP u).2 ?_))
    have := (Finset.mem_sdiff.1 hu).2
    rw [mem_pair_iff, not_or] at this
    exact this
  rw [h0, h1, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, bUnit_card,
    Finset.card_pair (Ne.symm ha)]
  omega

/-- Swapping the pair preserves the anti-associator (conjugate the equation). -/
theorem anti_swap {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m) (r : BUnit m)
    (h : Anti a b r) : Anti b a r := by
  unfold Anti at h ⊢
  have h' := congrArg conj h
  rw [conj_mul, conj_mul, conj_neg, conj_mul, conj_mul, conj_beval_of_ne ha,
    conj_beval_of_ne hb] at h'
  rcases basisUnit_conj (beval_basis r) with hr | hr
  · rw [hr] at h'
    simp only [neg_mul, mul_neg, neg_neg] at h'
    exact neg_eq_comm'.1 h'.symm
  · rw [hr] at h'
    simp only [neg_mul, mul_neg, neg_neg] at h'
    exact h'.symm

theorem N_symm {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m) :
    N a b = N b a :=
  sum_ite_congr (fun r => ⟨anti_swap ha hb r, anti_swap hb ha r⟩)

/-- Recursion, both lower (BDI Lemma 8.9 for basis units). -/
theorem N_LL {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n) (hab : a ≠ b) :
    N (BUnit.lower a) (BUnit.lower b) = 2 * N a b + 4 := by
  rw [N_succ, sum_ite_congr (key_LL_lower a b), ← N_def,
    count_anti ha hb hab _ (Hset a b) (subset_refl _) (class_LL_upper ha hb hab),
    Hset_card ha hb hab]
  omega

/-- Recursion, lower/upper with distinct imaginary a, b (BDI Lemma 8.10). -/
theorem N_LU_gen {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n) (hab : a ≠ b) :
    N (BUnit.lower a) (BUnit.upper b) + 2 * N a b + 4 = 2 ^ (n + 1) := by
  have hS1 : ({b, bxor a b} : Finset (BUnit n)) ⊆ Hset a b := by
    intro u hu
    rcases mem_pair_iff.1 hu with rfl | rfl
    · exact mem_Hset.2 (Or.inr (Or.inr (Or.inl rfl)))
    · exact mem_Hset.2 (Or.inr (Or.inr (Or.inr rfl)))
  have hS2 : ({bone n, a} : Finset (BUnit n)) ⊆ Hset a b := by
    intro u hu
    rcases mem_pair_iff.1 hu with rfl | rfl
    · exact mem_Hset.2 (Or.inl rfl)
    · exact mem_Hset.2 (Or.inr (Or.inl rfl))
  have h1 := count_not_anti ha hb hab _ _ hS1
    (fun u => (class_LU_lower ha hb hab u).trans (or_congr_left mem_pair_iff.symm))
  have h2 := count_not_anti ha hb hab _ _ hS2
    (fun u => (class_LU_upper ha hb hab u).trans (or_congr_left mem_pair_iff.symm))
  rw [Finset.card_pair (b_ne_bxor ha)] at h1
  rw [Finset.card_pair (Ne.symm ha)] at h2
  rw [N_succ, pow_succ]
  omega

/-- Recursion, (a,0) against (0,1): the maximum. -/
theorem N_LU_bone {n : ℕ} {a : BUnit n} (ha : a ≠ bone n) :
    N (BUnit.lower a) (BUnit.upper (bone n)) + 4 = 2 ^ (n + 1) := by
  have h1 := count_two ha _ (class_LU_bone_lower ha)
  have h2 := count_two ha _ (class_LU_bone_upper ha)
  rw [N_succ, pow_succ]
  omega

/-- Recursion, (a,0) against (0,a): the maximum. -/
theorem N_LU_self {n : ℕ} {a : BUnit n} (ha : a ≠ bone n) :
    N (BUnit.lower a) (BUnit.upper a) + 4 = 2 ^ (n + 1) := by
  have h1 := count_two ha _ (class_LU_self_lower ha)
  have h2 := count_two ha _ (class_LU_self_upper ha)
  rw [N_succ, pow_succ]
  omega

/-- Recursion, both upper with distinct imaginary a, b. -/
theorem N_UU_gen {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n) (hab : a ≠ b) :
    N (BUnit.upper a) (BUnit.upper b) = 2 * N a b + 4 := by
  have hS1 : ({a, b} : Finset (BUnit n)) ⊆ Hset a b := by
    intro u hu
    rcases mem_pair_iff.1 hu with rfl | rfl
    · exact mem_Hset.2 (Or.inr (Or.inl rfl))
    · exact mem_Hset.2 (Or.inr (Or.inr (Or.inl rfl)))
  have hS2 : ({bone n, bxor a b} : Finset (BUnit n)) ⊆ Hset a b := by
    intro u hu
    rcases mem_pair_iff.1 hu with rfl | rfl
    · exact mem_Hset.2 (Or.inl rfl)
    · exact mem_Hset.2 (Or.inr (Or.inr (Or.inr rfl)))
  have h1 := count_anti ha hb hab _ _ hS1
    (fun u => (class_UU_lower ha hb hab u).trans (or_congr_left mem_pair_iff.symm))
  have h2 := count_anti ha hb hab _ _ hS2
    (fun u => (class_UU_upper ha hb hab u).trans (or_congr_left mem_pair_iff.symm))
  rw [Finset.card_pair hab] at h1
  rw [Finset.card_pair (bone_ne_bxor hab)] at h2
  rw [N_succ]
  omega

/-- Recursion, (0,1) against (0,b): the maximum. -/
theorem N_UU_bone {n : ℕ} {b : BUnit n} (hb : b ≠ bone n) :
    N (BUnit.upper (bone n)) (BUnit.upper b) + 4 = 2 ^ (n + 1) := by
  have h1 := count_two hb _ (class_UU_bone_lower hb)
  have h2 := count_two hb _ (class_UU_bone_upper hb)
  rw [N_succ, pow_succ]
  omega

/-- **The birth function**: the recursion on the bit strings of the two indices. -/
def birth : ∀ {m : ℕ}, BUnit m → BUnit m → ℕ
  | 0, _, _ => 0
  | n + 1, BUnit.lower a, BUnit.lower b => 2 * birth a b + 4
  | n + 1, BUnit.lower a, BUnit.upper b =>
      if b = bone n ∨ b = a then 2 ^ (n + 1) - 4 else 2 ^ (n + 1) - 2 * birth a b - 4
  | n + 1, BUnit.upper a, BUnit.lower b =>
      if a = bone n ∨ a = b then 2 ^ (n + 1) - 4 else 2 ^ (n + 1) - 2 * birth a b - 4
  | n + 1, BUnit.upper a, BUnit.upper b =>
      if a = bone n ∨ b = bone n then 2 ^ (n + 1) - 4 else 2 * birth a b + 4

theorem birth_LL {n : ℕ} (a b : BUnit n) :
    birth (BUnit.lower a) (BUnit.lower b) = 2 * birth a b + 4 := rfl

theorem birth_LU {n : ℕ} (a b : BUnit n) :
    birth (BUnit.lower a) (BUnit.upper b)
      = if b = bone n ∨ b = a then 2 ^ (n + 1) - 4 else 2 ^ (n + 1) - 2 * birth a b - 4 := rfl

theorem birth_UL {n : ℕ} (a b : BUnit n) :
    birth (BUnit.upper a) (BUnit.lower b)
      = if a = bone n ∨ a = b then 2 ^ (n + 1) - 4 else 2 ^ (n + 1) - 2 * birth a b - 4 := rfl

theorem birth_UU {n : ℕ} (a b : BUnit n) :
    birth (BUnit.upper a) (BUnit.upper b)
      = if a = bone n ∨ b = bone n then 2 ^ (n + 1) - 4 else 2 * birth a b + 4 := rfl

theorem lower_ne_bone {n : ℕ} {a : BUnit n} (h : BUnit.lower a ≠ bone (n + 1)) : a ≠ bone n :=
  fun h' => h (by rw [h']; rfl)

theorem lower_inj' {n : ℕ} {a b : BUnit n} (h : BUnit.lower a ≠ BUnit.lower b) : a ≠ b :=
  fun h' => h (by rw [h'])

theorem upper_inj' {n : ℕ} {a b : BUnit n} (h : BUnit.upper a ≠ BUnit.upper b) : a ≠ b :=
  fun h' => h (by rw [h'])

theorem upper_ne_bone {n : ℕ} (a : BUnit n) : BUnit.upper a ≠ bone (n + 1) := by
  intro h
  cases h

/-- **Birth theorem (count form)**: for distinct imaginary indices, the
anti-associator count is the birth function. -/
theorem N_eq_birth : ∀ {m : ℕ} (a b : BUnit m),
    a ≠ bone m → b ≠ bone m → a ≠ b → N a b = birth a b
  | 0, BUnit.real0, _, ha, _, _ => absurd rfl ha
  | n + 1, BUnit.lower a, BUnit.lower b, ha, hb, hab => by
      have ha' := lower_ne_bone ha
      have hb' := lower_ne_bone hb
      have hab' := lower_inj' hab
      rw [birth_LL, N_LL ha' hb' hab', N_eq_birth a b ha' hb' hab']
  | n + 1, BUnit.lower a, BUnit.upper b, ha, _, _ => by
      have ha' := lower_ne_bone ha
      rw [birth_LU]
      by_cases hb1 : b = bone n
      · rw [if_pos (Or.inl hb1), hb1]
        have := N_LU_bone ha'
        omega
      · by_cases hba : b = a
        · rw [if_pos (Or.inr hba), hba]
          have := N_LU_self ha'
          omega
        · rw [if_neg (not_or.2 ⟨hb1, hba⟩)]
          have h := N_LU_gen ha' hb1 (Ne.symm hba)
          rw [N_eq_birth a b ha' hb1 (Ne.symm hba)] at h
          omega
  | n + 1, BUnit.upper a, BUnit.lower b, _, hb, _ => by
      have hb' := lower_ne_bone hb
      rw [birth_UL, N_symm (upper_ne_bone a) hb]
      by_cases ha1 : a = bone n
      · rw [if_pos (Or.inl ha1), ha1]
        have := N_LU_bone hb'
        omega
      · by_cases hab : a = b
        · rw [if_pos (Or.inr hab), hab]
          have := N_LU_self hb'
          omega
        · rw [if_neg (not_or.2 ⟨ha1, hab⟩)]
          have h := N_LU_gen hb' ha1 (Ne.symm hab)
          rw [N_symm hb' ha1, N_eq_birth a b ha1 hb' hab] at h
          omega
  | n + 1, BUnit.upper a, BUnit.upper b, _, _, hab => by
      have hab' := upper_inj' hab
      rw [birth_UU]
      by_cases ha1 : a = bone n
      · rw [if_pos (Or.inl ha1), ha1]
        have hb1 : b ≠ bone n := fun h => hab' (ha1.trans h.symm)
        have := N_UU_bone hb1
        omega
      · by_cases hb1 : b = bone n
        · rw [if_pos (Or.inr hb1), N_symm (upper_ne_bone a) (upper_ne_bone b), hb1]
          have := N_UU_bone ha1
          omega
        · rw [if_neg (not_or.2 ⟨ha1, hb1⟩), N_UU_gen ha1 hb1 hab', N_eq_birth a b ha1 hb1 hab']

/-- **Birth theorem**: `dim ker W(e_a, e_b) = birth a b` for every pair of distinct
imaginary basis units, at every level of the Cayley–Dickson tower. -/
theorem finrank_ker_WA_birth {m : ℕ} (a b : BUnit m) (ha : a ≠ bone m) (hb : b ≠ bone m)
    (hab : a ≠ b) :
    Module.finrank ℝ (LinearMap.ker (WA (beval a) (beval b))) = birth a b := by
  rw [finrank_ker_WA_eq_N, N_eq_birth a b ha hb hab]

/-- Every distinct imaginary pair of basis units is indexed. -/
theorem exists_index {m : ℕ} {x y : CD m} (hbx : BasisUnit x) (hcx : conj x = neg x)
    (hby : BasisUnit y) (hcy : conj y = neg y) (hne : x ≠ y) :
    ∃ a b : BUnit m, beval a = x ∧ beval b = y ∧ a ≠ bone m ∧ b ≠ bone m ∧ a ≠ b := by
  obtain ⟨a, rfl⟩ := basisUnit_beval hbx
  obtain ⟨b, rfl⟩ := basisUnit_beval hby
  refine ⟨a, b, rfl, rfl, ?_, ?_, fun h => hne (by rw [h])⟩
  · rintro rfl
    rw [conj_beval_bone] at hcx
    exact beval_ne_neg_self _ hcx
  · rintro rfl
    rw [conj_beval_bone] at hcy
    exact beval_ne_neg_self _ hcy

/-- Birth theorem, element form. -/
theorem finrank_ker_WA_birth' {m : ℕ} {x y : CD m} (hbx : BasisUnit x) (hcx : conj x = neg x)
    (hby : BasisUnit y) (hcy : conj y = neg y) (hne : x ≠ y) :
    ∃ a b : BUnit m, beval a = x ∧ beval b = y ∧
      Module.finrank ℝ (LinearMap.ker (WA x y)) = birth a b := by
  obtain ⟨a, b, rfl, rfl, ha, hb, hab⟩ := exists_index hbx hcx hby hcy hne
  exact ⟨a, b, rfl, rfl, finrank_ker_WA_birth a b ha hb hab⟩

/-! ### Arithmetic corollaries of the recursion -/

theorem one_le_of_ne_bone {m : ℕ} {a : BUnit m} (ha : a ≠ bone m) : 1 ≤ m := by
  cases m with
  | zero => cases a; exact absurd rfl ha
  | succ n => exact Nat.succ_pos n

theorem pow_succ_eq {n : ℕ} (hn : 1 ≤ n) : 2 ^ (n + 1) = 2 ^ (n - 1) * 4 := by
  rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
  rfl

/-- Every birth value is a multiple of 4 and at most `2^m − 4`. -/
theorem birth_props : ∀ {m : ℕ} (a b : BUnit m), a ≠ bone m → b ≠ bone m → a ≠ b →
    birth a b % 4 = 0 ∧ birth a b + 4 ≤ 2 ^ m
  | 0, BUnit.real0, _, ha, _, _ => absurd rfl ha
  | n + 1, BUnit.lower a, BUnit.lower b, ha, hb, hab => by
      have ih := birth_props a b (lower_ne_bone ha) (lower_ne_bone hb) (lower_inj' hab)
      rw [birth_LL, pow_succ]
      omega
  | n + 1, BUnit.lower a, BUnit.upper b, ha, _, _ => by
      have ha' := lower_ne_bone ha
      have h4 := pow_succ_eq (one_le_of_ne_bone ha')
      have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
      have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      rw [birth_LU]
      split_ifs with h
      · omega
      · have ih := birth_props a b ha' (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'.symm))
        omega
  | n + 1, BUnit.upper a, BUnit.lower b, _, hb, _ => by
      have hb' := lower_ne_bone hb
      have h4 := pow_succ_eq (one_le_of_ne_bone hb')
      have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
      have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      rw [birth_UL]
      split_ifs with h
      · omega
      · have ih := birth_props a b (fun h' => h (Or.inl h')) hb' (fun h' => h (Or.inr h'))
        omega
  | n + 1, BUnit.upper a, BUnit.upper b, _, _, hab => by
      have hab' := upper_inj' hab
      rw [birth_UU]
      split_ifs with h
      · have hn : 1 ≤ n := by
          rcases h with h | h
          · exact one_le_of_ne_bone (fun h' : b = bone n => hab' (h.trans h'.symm))
          · exact one_le_of_ne_bone (fun h' : a = bone n => hab' (h'.trans h.symm))
        have h4 := pow_succ_eq hn
        have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
        omega
      · have ih := birth_props a b (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h')) hab'
        rw [pow_succ]
        omega

/-- From the octonions on, every birth value is `4·(odd)`: `birth ≡ 4 (mod 8)`. -/
theorem birth_mod_eight : ∀ {n : ℕ} (a b : BUnit (n + 3)),
    a ≠ bone (n + 3) → b ≠ bone (n + 3) → a ≠ b → birth a b % 8 = 4
  | n, BUnit.lower a, BUnit.lower b, ha, hb, hab => by
      have ih := birth_props a b (lower_ne_bone ha) (lower_ne_bone hb) (lower_inj' hab)
      rw [birth_LL]
      omega
  | n, BUnit.lower a, BUnit.upper b, ha, _, _ => by
      have ha' := lower_ne_bone ha
      have h8 : 2 ^ (n + 2 + 1) = 2 ^ n * 8 := by
        rw [show n + 2 + 1 = n + 3 by rfl, pow_add]; rfl
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [birth_LU]
      split_ifs with h
      · omega
      · have ih := birth_props a b ha' (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'.symm))
        have h4 : 2 ^ (n + 2) = 2 ^ n * 4 := by rw [pow_add]; rfl
        omega
  | n, BUnit.upper a, BUnit.lower b, _, hb, _ => by
      have hb' := lower_ne_bone hb
      have h8 : 2 ^ (n + 2 + 1) = 2 ^ n * 8 := by
        rw [show n + 2 + 1 = n + 3 by rfl, pow_add]; rfl
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [birth_UL]
      split_ifs with h
      · omega
      · have ih := birth_props a b (fun h' => h (Or.inl h')) hb' (fun h' => h (Or.inr h'))
        have h4 : 2 ^ (n + 2) = 2 ^ n * 4 := by rw [pow_add]; rfl
        omega
  | n, BUnit.upper a, BUnit.upper b, _, _, hab => by
      have hab' := upper_inj' hab
      have h8 : 2 ^ (n + 2 + 1) = 2 ^ n * 8 := by
        rw [show n + 2 + 1 = n + 3 by rfl, pow_add]; rfl
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [birth_UU]
      split_ifs with h
      · omega
      · have ih := birth_props a b (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h')) hab'
        omega

/-! ## Floor D: the annihilator of `z = e_a + e_b ℓ` has the birth dimension

`ker_Lz_iff_ker_W` (BDI Prop. 11.1 for unit pairs with unit art) says the pair
`(u, v)` is killed by left multiplication by `z = (e_a, e_b)` iff `v = (e_a u) e_b`
and `W(e_a, e_b) u = 0`. The lift `u ↦ (u, (e_a u) e_b)` is an injective linear map,
so `ker L_z = (ker W).map lift` and the dimensions agree. -/

/-- The lift `u ↦ (u, (x u) y)` as a linear map. -/
def annLift {m : ℕ} (x y : CD m) : CD m →ₗ[ℝ] CD (m + 1) :=
  cdPairLm.comp (LinearMap.prod LinearMap.id ((mulRight y).comp (mulLeft x)))

theorem annLift_apply {m : ℕ} (x y u : CD m) : annLift x y u = dbl u ((x * u) * y) := rfl

theorem annLift_injective {m : ℕ} (x y : CD m) : Function.Injective (annLift x y) := by
  intro u v h
  have h' : dbl u ((x * u) * y) = dbl v ((x * v) * y) := h
  injection h' with _ h1 _

theorem ker_mulLeft_dbl_eq_map {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m) :
    LinearMap.ker (mulLeft (dbl (beval a) (beval b)))
      = (LinearMap.ker (WA (beval a) (beval b))).map (annLift (beval a) (beval b)) := by
  ext w
  cases w with
  | dbl u v =>
    rw [LinearMap.mem_ker, Submodule.mem_map]
    have key := ker_Lz_iff_ker_W (beval a) (beval b) (lart a) (rart b) (conj_beval_of_ne ha)
      (conj_beval_of_ne hb) (sq_beval ha) (sq_beval hb) u v
    constructor
    · intro h
      obtain ⟨hv, hw⟩ := key.1 h
      refine ⟨u, ?_, ?_⟩
      · rw [LinearMap.mem_ker]; exact hw
      · rw [annLift_apply, hv]
    · rintro ⟨u', hu', he⟩
      rw [annLift_apply] at he
      injection he with _ h1 h2
      subst h1
      exact key.2 ⟨h2.symm, hu'⟩

/-- **Annihilator theorem**: `dim ker L_{e_a + e_b ℓ} = birth a b` at level `m + 1`. -/
theorem finrank_ann_birth {m : ℕ} (a b : BUnit m) (ha : a ≠ bone m) (hb : b ≠ bone m)
    (hab : a ≠ b) :
    Module.finrank ℝ (LinearMap.ker (mulLeft (dbl (beval a) (beval b)))) = birth a b := by
  rw [ker_mulLeft_dbl_eq_map ha hb, ← finrank_ker_WA_birth a b ha hb hab]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (annLift_injective _ _) _)).symm

/-- From the octonions on, `birth` never vanishes. -/
theorem birth_ne_zero {n : ℕ} (a b : BUnit (n + 3)) (ha : a ≠ bone (n + 3))
    (hb : b ≠ bone (n + 3)) (hab : a ≠ b) : birth a b ≠ 0 := by
  have := birth_mod_eight a b ha hb hab
  omega

/-- **Zero divisors, eternal**: at every level `≥ 4`, `z = e_a + e_b ℓ` (distinct
imaginary `a, b`) has a non-zero annihilator. -/
theorem exists_annihilator {n : ℕ} (a b : BUnit (n + 3)) (ha : a ≠ bone (n + 3))
    (hb : b ≠ bone (n + 3)) (hab : a ≠ b) :
    ∃ w : CD (n + 4), w ≠ 0 ∧ dbl (beval a) (beval b) * w = 0 := by
  by_contra hcon
  have hker : LinearMap.ker (mulLeft (dbl (beval a) (beval b))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    exact hcon ⟨w, hne, hw⟩
  have h := finrank_ann_birth a b ha hb hab
  rw [hker, finrank_bot] at h
  exact birth_ne_zero a b ha hb hab h.symm

/-! ## Census check (computable): histogram of `birth` over unordered imaginary pairs -/

/-- Number of ordered pairs of distinct imaginary indices at level `m` with `birth = v`. -/
def birthCount (m v : ℕ) : ℕ :=
  (Finset.univ.filter fun p : BUnit m × BUnit m =>
    p.1 ≠ bone m ∧ p.2 ≠ bone m ∧ p.1 ≠ p.2 ∧ birth p.1 p.2 = v).card

/-- Histogram over unordered pairs, values `4, 12, …, 2^m − 4`. -/
def birthHistogram (m : ℕ) : List (ℕ × ℕ) :=
  (List.range (2 ^ (m - 3))).map fun k => (8 * k + 4, birthCount m (8 * k + 4) / 2)

/-! ## Closed form (signed-digit unwinding of the recursion) — checked by evaluation, NOT a theorem

Read the index of `e_p` as a bit string. Let `J = max(lsb p, lsb q, lsb (p xor q))`
(lowest set bits). Then `birth p q = 2^(m-1) + T_m` where `T_(J+1) = 2^J − 4` and, for
`k = J+2, …, m`, `T_k = σ_(k-1) · (2 T_(k-1) + 4)` with `σ_j = +1` if bit `j` of `p xor q`
is 0 and `−1` otherwise. `closedCheck m` compares this with `birth` on every pair. -/

def toNat : ∀ {m : ℕ}, BUnit m → ℕ
  | 0, BUnit.real0 => 0
  | n + 1, BUnit.lower u => toNat u
  | n + 1, BUnit.upper u => toNat u + 2 ^ n

/-- Index of the lowest set bit (`0` for `0`, by fuel). -/
def lsb : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, p => if p % 2 = 1 ∨ p = 0 then 0 else 1 + lsb fuel (p / 2)

def birthClosed (m p q : ℕ) : ℤ :=
  let pq := p ^^^ q
  let J := max (lsb m p) (max (lsb m q) (lsb m pq))
  let T0 : ℤ := 2 ^ J - 4
  let T := (List.range (m - (J + 1))).foldl
    (fun T i => (if (pq >>> (J + 1 + i)) % 2 = 1 then (-1 : ℤ) else 1) * (2 * T + 4)) T0
  2 ^ (m - 1) + T

def closedCheck (m : ℕ) : Bool :=
  (Finset.univ : Finset (BUnit m × BUnit m)).filter (fun p =>
    p.1 ≠ bone m ∧ p.2 ≠ bone m ∧ p.1 ≠ p.2 ∧
      (birth p.1 p.2 : ℤ) ≠ birthClosed m (toNat p.1) (toNat p.2)) = ∅

/-! ## Closed form, sealed: the signed-digit unwinding as a theorem

The same formula, read structurally off the bit string. `lsbB u` is the position of
the lowest set bit of the index `u` (`m` for `bone m`, which has none). `Jlev a b =
max (lsbB a, lsbB b, lsbB (a xor b))` is the level below the one at which the recursion
first hits the maximum. `Tclosed d j` unwinds the recursion along the bits of
`d = a xor b` above `j`:

  T_(j+1) = 2^j − 4,    T_k = σ_(k−1) (2 T_(k−1) + 4)   for k = j+2, …, m,

with `σ_(k−1) = +1` if bit `k−1` of `d` is `0` (the leading bits of `a`, `b` agree) and
`−1` if it is `1`. `birth_closed` is the paper's equation (9). -/

def lsbB : ∀ {m : ℕ}, BUnit m → ℕ
  | 0, _ => 0
  | n + 1, BUnit.lower u => if u = bone n then n + 1 else lsbB u
  | n + 1, BUnit.upper u => lsbB u

theorem lsbB_bone : ∀ m : ℕ, lsbB (bone m) = m
  | 0 => rfl
  | n + 1 => by
      show lsbB (BUnit.lower (bone n)) = n + 1
      simp [lsbB]

theorem lsbB_lower_of_ne {n : ℕ} {u : BUnit n} (h : u ≠ bone n) :
    lsbB (BUnit.lower u) = lsbB u := by
  simp [lsbB, h]

theorem lsbB_upper {n : ℕ} (u : BUnit n) : lsbB (BUnit.upper u) = lsbB u := rfl

theorem lsbB_le : ∀ {m : ℕ} (u : BUnit m), lsbB u ≤ m
  | 0, BUnit.real0 => le_refl 0
  | n + 1, BUnit.lower u => by
      by_cases h : u = bone n
      · subst h
        exact le_of_eq (lsbB_bone (n + 1))
      · rw [lsbB_lower_of_ne h]
        exact Nat.le_succ_of_le (lsbB_le u)
  | n + 1, BUnit.upper u => Nat.le_succ_of_le (lsbB_le u)

theorem lsbB_lt : ∀ {m : ℕ} (u : BUnit m), u ≠ bone m → lsbB u < m
  | 0, BUnit.real0, h => absurd rfl h
  | n + 1, BUnit.lower u, h => by
      have hu : u ≠ bone n := lower_ne_bone h
      rw [lsbB_lower_of_ne hu]
      exact Nat.lt_succ_of_lt (lsbB_lt u hu)
  | n + 1, BUnit.upper u, _ => by
      rw [lsbB_upper]
      exact Nat.lt_succ_of_le (lsbB_le u)

/-- The start level of the closed form: `J = max(lsb a, lsb b, lsb (a xor b))`. -/
def Jlev {m : ℕ} (a b : BUnit m) : ℕ := max (lsbB a) (max (lsbB b) (lsbB (bxor a b)))

/-- The unwinding `T_m` of the recursion along the bits of `d = a xor b` above `j`. -/
def Tclosed : ∀ {m : ℕ}, BUnit m → ℕ → ℤ
  | 0, _, _ => 0
  | n + 1, BUnit.lower d, j => if n = j then 2 ^ j - 4 else 2 * Tclosed d j + 4
  | n + 1, BUnit.upper d, j => if n = j then 2 ^ j - 4 else -(2 * Tclosed d j + 4)

theorem Tclosed_lower {n : ℕ} (d : BUnit n) (j : ℕ) :
    Tclosed (BUnit.lower d) j = if n = j then 2 ^ j - 4 else 2 * Tclosed d j + 4 := rfl

theorem Tclosed_upper {n : ℕ} (d : BUnit n) (j : ℕ) :
    Tclosed (BUnit.upper d) j = if n = j then 2 ^ j - 4 else -(2 * Tclosed d j + 4) := rfl

theorem bxor_lower_lower {n : ℕ} (a b : BUnit n) :
    bxor (BUnit.lower a) (BUnit.lower b) = BUnit.lower (bxor a b) := rfl
theorem bxor_lower_upper {n : ℕ} (a b : BUnit n) :
    bxor (BUnit.lower a) (BUnit.upper b) = BUnit.upper (bxor a b) := rfl
theorem bxor_upper_lower {n : ℕ} (a b : BUnit n) :
    bxor (BUnit.upper a) (BUnit.lower b) = BUnit.upper (bxor a b) := rfl
theorem bxor_upper_upper {n : ℕ} (a b : BUnit n) :
    bxor (BUnit.upper a) (BUnit.upper b) = BUnit.lower (bxor a b) := rfl

theorem bxor_ne_bone {n : ℕ} {a b : BUnit n} (hab : a ≠ b) : bxor a b ≠ bone n :=
  fun h => hab (bxor_eq_bone_iff.mp h)

theorem Jlev_lt {n : ℕ} (a b : BUnit n) (ha : a ≠ bone n) (hb : b ≠ bone n) (hab : a ≠ b) :
    Jlev a b < n := by
  unfold Jlev
  have h1 := lsbB_lt a ha
  have h2 := lsbB_lt b hb
  have h3 := lsbB_lt _ (bxor_ne_bone hab)
  omega

theorem Jlev_LL {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n) (hab : a ≠ b) :
    Jlev (BUnit.lower a) (BUnit.lower b) = Jlev a b := by
  unfold Jlev
  rw [bxor_lower_lower, lsbB_lower_of_ne ha, lsbB_lower_of_ne hb,
    lsbB_lower_of_ne (bxor_ne_bone hab)]

theorem Jlev_LU {n : ℕ} {a : BUnit n} (b : BUnit n) (ha : a ≠ bone n) :
    Jlev (BUnit.lower a) (BUnit.upper b) = Jlev a b := by
  unfold Jlev
  rw [bxor_lower_upper, lsbB_lower_of_ne ha, lsbB_upper, lsbB_upper]

theorem Jlev_UL {n : ℕ} (a : BUnit n) {b : BUnit n} (hb : b ≠ bone n) :
    Jlev (BUnit.upper a) (BUnit.lower b) = Jlev a b := by
  unfold Jlev
  rw [bxor_upper_lower, lsbB_lower_of_ne hb, lsbB_upper, lsbB_upper]

theorem Jlev_UU {n : ℕ} {a b : BUnit n} (hab : a ≠ b) :
    Jlev (BUnit.upper a) (BUnit.upper b) = Jlev a b := by
  unfold Jlev
  rw [bxor_upper_upper, lsbB_upper, lsbB_upper, lsbB_lower_of_ne (bxor_ne_bone hab)]

/-- At the level where the maximum is hit, `J` is the level below. -/
theorem Jlev_LU_max {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (h : b = bone n ∨ b = a) :
    Jlev (BUnit.lower a) (BUnit.upper b) = n := by
  unfold Jlev
  rw [bxor_lower_upper, lsbB_lower_of_ne ha, lsbB_upper, lsbB_upper]
  have h1 := lsbB_le a
  have h3 := lsbB_le (bxor a b)
  rcases h with h | h
  · subst h
    rw [lsbB_bone]
    omega
  · subst h
    rw [bxor_self, lsbB_bone]
    omega

theorem Jlev_UL_max {n : ℕ} {a b : BUnit n} (hb : b ≠ bone n) (h : a = bone n ∨ a = b) :
    Jlev (BUnit.upper a) (BUnit.lower b) = n := by
  unfold Jlev
  rw [bxor_upper_lower, lsbB_lower_of_ne hb, lsbB_upper, lsbB_upper]
  have h2 := lsbB_le b
  have h3 := lsbB_le (bxor a b)
  rcases h with h | h
  · subst h
    rw [lsbB_bone]
    omega
  · subst h
    rw [bxor_self, lsbB_bone]
    omega

theorem Jlev_UU_max {n : ℕ} {a b : BUnit n} (hab : a ≠ b) (h : a = bone n ∨ b = bone n) :
    Jlev (BUnit.upper a) (BUnit.upper b) = n := by
  unfold Jlev
  rw [bxor_upper_upper, lsbB_upper, lsbB_upper, lsbB_lower_of_ne (bxor_ne_bone hab)]
  have h1 := lsbB_le a
  have h2 := lsbB_le b
  have h3 := lsbB_le (bxor a b)
  rcases h with h | h
  · subst h
    rw [lsbB_bone] at h1 ⊢
    omega
  · subst h
    rw [lsbB_bone] at h2 ⊢
    omega

/-- **Closed form (sealed)**: equation (9) of the paper. For distinct imaginary indices,
`birth a b = 2^(m−1) + T_m` with `T_(J+1) = 2^J − 4` and `T_k = σ_(k−1)(2 T_(k−1) + 4)`. -/
theorem birth_closed : ∀ {m : ℕ} (a b : BUnit m), a ≠ bone m → b ≠ bone m → a ≠ b →
    (birth a b : ℤ) = 2 ^ (m - 1) + Tclosed (bxor a b) (Jlev a b)
  | 0, BUnit.real0, _, ha, _, _ => absurd rfl ha
  | n + 1, BUnit.lower a, BUnit.lower b, ha, hb, hab => by
      have ha' := lower_ne_bone ha
      have hb' := lower_ne_bone hb
      have hab' := lower_inj' hab
      have ih := birth_closed a b ha' hb' hab'
      have hJ := Jlev_lt a b ha' hb' hab'
      have hn := one_le_of_ne_bone ha'
      have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hn]
      rw [birth_LL, Nat.add_sub_cancel, Jlev_LL ha' hb' hab', bxor_lower_lower, Tclosed_lower,
        if_neg (by omega)]
      push_cast
      rw [ih, h2]
      ring
  | n + 1, BUnit.lower a, BUnit.upper b, ha, _, _ => by
      have ha' := lower_ne_bone ha
      have hn := one_le_of_ne_bone ha'
      have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hn]
      have h4 : 4 ≤ 2 ^ (n + 1) := by
        have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
        rw [pow_succ_eq hn]
        omega
      rw [birth_LU, Nat.add_sub_cancel, bxor_lower_upper]
      split_ifs with h
      · rw [Jlev_LU_max ha' h, Tclosed_upper, if_pos rfl, Nat.cast_sub h4]
        push_cast
        rw [pow_succ]
        ring
      · push_neg at h
        have hb' := h.1
        have hab' : a ≠ b := fun e => h.2 e.symm
        have ih := birth_closed a b ha' hb' hab'
        have hJ := Jlev_lt a b ha' hb' hab'
        have hbd := (birth_props a b ha' hb' hab').2
        have hsub : 2 * birth a b + 4 ≤ 2 ^ (n + 1) := by
          rw [pow_succ]
          omega
        rw [Jlev_LU b ha', Tclosed_upper, if_neg (by omega), Nat.sub_sub, Nat.cast_sub hsub]
        push_cast
        rw [ih, pow_succ, h2]
        ring
  | n + 1, BUnit.upper a, BUnit.lower b, _, hb, _ => by
      have hb' := lower_ne_bone hb
      have hn := one_le_of_ne_bone hb'
      have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hn]
      have h4 : 4 ≤ 2 ^ (n + 1) := by
        have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
        rw [pow_succ_eq hn]
        omega
      rw [birth_UL, Nat.add_sub_cancel, bxor_upper_lower]
      split_ifs with h
      · rw [Jlev_UL_max hb' h, Tclosed_upper, if_pos rfl, Nat.cast_sub h4]
        push_cast
        rw [pow_succ]
        ring
      · push_neg at h
        have ha' := h.1
        have hab' : a ≠ b := h.2
        have ih := birth_closed a b ha' hb' hab'
        have hJ := Jlev_lt a b ha' hb' hab'
        have hbd := (birth_props a b ha' hb' hab').2
        have hsub : 2 * birth a b + 4 ≤ 2 ^ (n + 1) := by
          rw [pow_succ]
          omega
        rw [Jlev_UL a hb', Tclosed_upper, if_neg (by omega), Nat.sub_sub, Nat.cast_sub hsub]
        push_cast
        rw [ih, pow_succ, h2]
        ring
  | n + 1, BUnit.upper a, BUnit.upper b, _, _, hab => by
      have hab' := upper_inj' hab
      rw [birth_UU, Nat.add_sub_cancel, bxor_upper_upper]
      split_ifs with h
      · have hn : 1 ≤ n := by
          rcases h with h | h
          · exact one_le_of_ne_bone (fun h' : b = bone n => hab' (h.trans h'.symm))
          · exact one_le_of_ne_bone (fun h' : a = bone n => hab' (h'.trans h.symm))
        have h4 : 4 ≤ 2 ^ (n + 1) := by
          have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
          rw [pow_succ_eq hn]
          omega
        rw [Jlev_UU_max hab' h, Tclosed_lower, if_pos rfl, Nat.cast_sub h4]
        push_cast
        rw [pow_succ]
        ring
      · push_neg at h
        have ha' := h.1
        have hb' := h.2
        have ih := birth_closed a b ha' hb' hab'
        have hJ := Jlev_lt a b ha' hb' hab'
        have hn := one_le_of_ne_bone ha'
        have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hn]
        rw [Jlev_UU hab', Tclosed_lower, if_neg (by omega)]
        push_cast
        rw [ih, h2]
        ring

/-! ## Floor F: the four-lift sum rule and the total of birth

For a pair `(a,b)` of distinct imaginary indices at level `n`, its four lifts to level
`n+1` have birth values summing to `2^(n+2)`, independently of `birth a b`: the two
"agree" lifts `((a,0),(b,0))`, `((0,a),(0,b))` contribute `2·birth + 4` each and the two
"differ" lifts `((a,0),(0,b))`, `((0,a),(b,0))` contribute `2^(n+1) − 2·birth − 4` each,
so `birth a b` cancels. Summing over all pairs, the total of `birth` over ordered distinct
imaginary pairs at level `n+1` is `4·8^n − 28·2^n + 24 = 4(2^n + 3)(2^n − 1)(2^n − 2)`, with
no dependence on the level-`n` total. By `zhilina_degree_eq_birth` this total is the
number of edges of the two-sided zero-divisor graph on doubly pure unit-pair lines of
`A_(n+2)`: `168` for the sedenion graph (`n = 1`), `1848`, `15960`, … -/

theorem birth_four_lifts {n : ℕ} {a b : BUnit n} (ha : a ≠ bone n) (hb : b ≠ bone n)
    (hab : a ≠ b) :
    birth (BUnit.lower a) (BUnit.lower b) + birth (BUnit.lower a) (BUnit.upper b)
      + birth (BUnit.upper a) (BUnit.lower b) + birth (BUnit.upper a) (BUnit.upper b)
      = 2 ^ (n + 2) := by
  have hbd := (birth_props a b ha hb hab).2
  have h1 : ¬ (b = bone n ∨ b = a) := by
    rintro (h | h)
    · exact hb h
    · exact hab h.symm
  have h2 : ¬ (a = bone n ∨ a = b) := by
    rintro (h | h)
    · exact ha h
    · exact hab h
  have h3 : ¬ (a = bone n ∨ b = bone n) := by
    rintro (h | h)
    · exact ha h
    · exact hb h
  rw [birth_LL, birth_LU, birth_UL, birth_UU, if_neg h1, if_neg h2, if_neg h3]
  have e1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have e2 : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_succ, pow_succ]; ring
  omega

/-- `birth` on ordered pairs, zero off the distinct-imaginary pairs. -/
def birthTerm {m : ℕ} (a b : BUnit m) : ℕ :=
  if a ≠ bone m ∧ b ≠ bone m ∧ a ≠ b then birth a b else 0

/-- Total of `birth` over ordered pairs of distinct imaginary indices at level `m`. -/
def birthTotal (m : ℕ) : ℕ := ∑ a : BUnit m, ∑ b : BUnit m, birthTerm a b

theorem lower_eq_bone_iff {n : ℕ} {a : BUnit n} : BUnit.lower a = bone (n + 1) ↔ a = bone n := by
  constructor
  · intro h
    have h' : BUnit.lower a = BUnit.lower (bone n) := h
    injection h' with hidx h1
  · intro h
    rw [h]
    rfl

theorem lower_eq_lower_iff {n : ℕ} {a b : BUnit n} : BUnit.lower a = BUnit.lower b ↔ a = b := by
  constructor
  · intro h
    injection h with hidx h1
  · intro h
    rw [h]

theorem upper_eq_upper_iff {n : ℕ} {a b : BUnit n} : BUnit.upper a = BUnit.upper b ↔ a = b := by
  constructor
  · intro h
    injection h with hidx h1
  · intro h
    rw [h]

theorem lower_ne_upper' {n : ℕ} (a b : BUnit n) : BUnit.lower a ≠ BUnit.upper b := by
  intro h
  cases h

theorem upper_ne_lower' {n : ℕ} (a b : BUnit n) : BUnit.upper a ≠ BUnit.lower b := by
  intro h
  cases h

theorem birthTerm_LL {n : ℕ} (a b : BUnit n) :
    birthTerm (BUnit.lower a) (BUnit.lower b)
      = if a ≠ bone n ∧ b ≠ bone n ∧ a ≠ b then 2 * birth a b + 4 else 0 := by
  unfold birthTerm
  rw [birth_LL]
  exact if_congr (by rw [ne_eq, lower_eq_bone_iff, ne_eq, lower_eq_bone_iff, ne_eq,
    lower_eq_lower_iff]) rfl rfl

theorem birthTerm_LU {n : ℕ} (a b : BUnit n) :
    birthTerm (BUnit.lower a) (BUnit.upper b)
      = if a ≠ bone n then
          (if b = bone n ∨ b = a then 2 ^ (n + 1) - 4 else 2 ^ (n + 1) - 2 * birth a b - 4)
        else 0 := by
  unfold birthTerm
  rw [birth_LU]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h, -, -⟩
    exact lower_ne_bone h
  · intro h
    exact ⟨fun e => h (lower_eq_bone_iff.mp e), upper_ne_bone b, lower_ne_upper' a b⟩

theorem birthTerm_UL {n : ℕ} (a b : BUnit n) :
    birthTerm (BUnit.upper a) (BUnit.lower b)
      = if b ≠ bone n then
          (if a = bone n ∨ a = b then 2 ^ (n + 1) - 4 else 2 ^ (n + 1) - 2 * birth a b - 4)
        else 0 := by
  unfold birthTerm
  rw [birth_UL]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨-, h, -⟩
    exact lower_ne_bone h
  · intro h
    exact ⟨upper_ne_bone a, fun e => h (lower_eq_bone_iff.mp e), upper_ne_lower' a b⟩

theorem birthTerm_UU {n : ℕ} (a b : BUnit n) :
    birthTerm (BUnit.upper a) (BUnit.upper b)
      = if a ≠ b then
          (if a = bone n ∨ b = bone n then 2 ^ (n + 1) - 4 else 2 * birth a b + 4)
        else 0 := by
  unfold birthTerm
  rw [birth_UU]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨-, -, h⟩
    exact fun e => h (by rw [e])
  · intro h
    exact ⟨upper_ne_bone a, upper_ne_bone b, fun e => h (upper_eq_upper_iff.mp e)⟩

/-- The four lifts of a pair, summed (zero contributions off the distinct-imaginary pairs). -/
def birthQuad {n : ℕ} (a b : BUnit n) : ℕ :=
  birthTerm (BUnit.lower a) (BUnit.lower b) + birthTerm (BUnit.lower a) (BUnit.upper b)
    + birthTerm (BUnit.upper a) (BUnit.lower b) + birthTerm (BUnit.upper a) (BUnit.upper b)

/-- Pointwise form of the sum rule, valid for every pair (degenerate pairs included),
with the corrections written as indicators so that it can be summed directly. -/
theorem birthTerm_four_lifts {n : ℕ} (a b : BUnit n) :
    birthQuad a b
      + 8 * (if a = bone n then 1 else 0) + 8 * (if b = bone n then 1 else 0)
      + 8 * (if a = b then 1 else 0)
      + 2 ^ (n + 2) * ((if a = bone n then 1 else 0) * (if b = bone n then 1 else 0))
      = 2 ^ (n + 2) + 24 * ((if a = bone n then 1 else 0) * (if b = bone n then 1 else 0)) := by
  have e1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have e2 : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_succ, pow_succ]; ring
  unfold birthQuad
  rw [birthTerm_LL, birthTerm_LU, birthTerm_UL, birthTerm_UU]
  by_cases ha : a = bone n
  · subst ha
    by_cases hb : b = bone n
    · subst hb
      simp
      omega
    · have hn := one_le_of_ne_bone hb
      have h4 : 4 ≤ 2 ^ (n + 1) := by
        have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
        rw [pow_succ_eq hn]
        omega
      simp [hb, Ne.symm hb]
      omega
  · by_cases hb : b = bone n
    · subst hb
      have hn := one_le_of_ne_bone ha
      have h4 : 4 ≤ 2 ^ (n + 1) := by
        have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
        rw [pow_succ_eq hn]
        omega
      simp [ha, Ne.symm ha]
      omega
    · by_cases hab : a = b
      · subst hab
        have hn := one_le_of_ne_bone ha
        have h4 : 4 ≤ 2 ^ (n + 1) := by
          have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
          rw [pow_succ_eq hn]
          omega
        simp [ha]
        omega
      · have hbd := (birth_props a b ha hb hab).2
        simp [ha, hb, hab, Ne.symm hab]
        omega

/-- The quadrant split of the total: level `n+1` as a double sum over level `n`. -/
theorem birthTotal_split (n : ℕ) :
    birthTotal (n + 1) = ∑ a : BUnit n, ∑ b : BUnit n, birthQuad a b := by
  unfold birthTotal
  rw [sum_succ_split (fun A => ∑ B : BUnit (n + 1), birthTerm A B)]
  simp only [sum_succ_split (fun B => birthTerm (BUnit.lower _) B),
    sum_succ_split (fun B => birthTerm (BUnit.upper _) B)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  unfold birthQuad
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem sum_ind_left (n c : ℕ) :
    ∑ a : BUnit n, ∑ _b : BUnit n, (c * if a = bone n then 1 else 0) = c * 2 ^ n := by
  classical
  simp only [Finset.sum_const, Finset.card_univ, bUnit_card, smul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq']
  simp
  ring

theorem sum_ind_right (n c : ℕ) :
    ∑ _a : BUnit n, ∑ b : BUnit n, (c * if b = bone n then 1 else 0) = c * 2 ^ n := by
  classical
  have h : ∑ b : BUnit n, (c * if b = bone n then 1 else 0) = c := by
    rw [← Finset.mul_sum, Finset.sum_ite_eq']
    simp
  simp only [h, Finset.sum_const, Finset.card_univ, bUnit_card, smul_eq_mul]
  ring

theorem sum_ind_diag (n c : ℕ) :
    ∑ a : BUnit n, ∑ b : BUnit n, (c * if a = b then 1 else 0) = c * 2 ^ n := by
  classical
  have h : ∀ a : BUnit n, ∑ b : BUnit n, (c * if a = b then 1 else 0) = c := fun a => by
    rw [← Finset.mul_sum, Finset.sum_ite_eq]
    simp
  simp only [h, Finset.sum_const, Finset.card_univ, bUnit_card, smul_eq_mul]
  ring

theorem sum_ind_both (n c : ℕ) :
    ∑ a : BUnit n, ∑ b : BUnit n,
      (c * ((if a = bone n then 1 else 0) * (if b = bone n then 1 else 0))) = c := by
  classical
  have h : ∀ a : BUnit n, ∑ b : BUnit n,
      (c * ((if a = bone n then 1 else 0) * (if b = bone n then 1 else 0)))
        = c * (if a = bone n then 1 else 0) := fun a => by
    simp only [← mul_assoc]
    rw [← Finset.mul_sum, Finset.sum_ite_eq']
    simp
  simp only [h]
  rw [← Finset.mul_sum, Finset.sum_ite_eq']
  simp

theorem sum_const_two (n c : ℕ) :
    ∑ _a : BUnit n, ∑ _b : BUnit n, c = 2 ^ n * (2 ^ n * c) := by
  simp only [Finset.sum_const, Finset.card_univ, bUnit_card, smul_eq_mul]

/-- **Total of birth (sealed).** `Σ birth` over ordered distinct imaginary pairs at level
`n+1` equals `4·8^n − 28·2^n + 24 = 4(2^n+3)(2^n−1)(2^n−2)`, written without subtraction. -/
theorem birthTotal_succ (n : ℕ) : birthTotal (n + 1) + 28 * 2 ^ n = 4 * 8 ^ n + 24 := by
  classical
  have hsum : ∑ a : BUnit n, ∑ b : BUnit n,
      (birthQuad a b
        + 8 * (if a = bone n then 1 else 0) + 8 * (if b = bone n then 1 else 0)
        + 8 * (if a = b then 1 else 0)
        + 2 ^ (n + 2) * ((if a = bone n then 1 else 0) * (if b = bone n then 1 else 0)))
      = ∑ a : BUnit n, ∑ b : BUnit n,
        (2 ^ (n + 2) + 24 * ((if a = bone n then 1 else 0) * (if b = bone n then 1 else 0))) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => birthTerm_four_lifts a b))
  simp only [Finset.sum_add_distrib] at hsum
  rw [← birthTotal_split, sum_ind_left, sum_ind_right, sum_ind_diag, sum_ind_both,
    sum_ind_both, sum_const_two] at hsum
  have e2 : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_succ, pow_succ]; ring
  have e8 : (8 : ℕ) ^ n = 2 ^ n * 2 ^ n * 2 ^ n := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  rw [e2] at hsum
  rw [e8]
  zify at hsum ⊢
  linear_combination hsum

/-! ## The spectrum of birth — closed form, checked by evaluation, NOT a theorem

Number of unordered pairs of distinct imaginary indices at level `m ≥ 3` with
`birth = 8k + 4`, for `0 ≤ k < 2^(m−3)`:

  H_m(k) = 21·2^(m−3)
         + Σ_{j=3}^{m−2} 3·2^(m−j−1)(2^j − 1)·[k < 2^(m−j−2)  or  k ≥ 2^(m−3) − 2^(m−j−2)]
         + 3·(2^(m−1) − 1)·[k = 2^(m−3) − 1].

Derivation (on paper, 2026-10-03): (1) the number of ordered pairs with `Jlev = j` and a
prescribed pattern of bits of `a xor b` above `j` is `3·2^(m−j)(2^j − 1)`, independent of the
pattern; (2) writing the bin index `k` as an `(m−3)`-bit string, the two clauses of `Tclosed`
act as `k ↦ 2k+1` (append 1) and `k ↦ 2(N−1−k)` (complement, append 0), so from the top bin
at level `j+1` the reachable bins at level `m` are exactly those whose first `j−1` bits are
equal; `J ≤ 2` pairs all pass through the single bin of level 3 and then reach every bin once.
`spectrumCheck m` compares the formula with `birthHistogram` (the sealed recursion); it is
`true` for `m = 3, …, 8`. -/

def birthSpectrum (m k : ℕ) : ℕ :=
  21 * 2 ^ (m - 3)
  + ((List.range (m - 4)).map fun i =>
      let j := i + 3
      if k < 2 ^ (m - 2 - j) ∨ 2 ^ (m - 3) ≤ k + 2 ^ (m - 2 - j)
      then 3 * 2 ^ (m - j - 1) * (2 ^ j - 1) else 0).sum
  + (if 4 ≤ m ∧ k + 1 = 2 ^ (m - 3) then 3 * (2 ^ (m - 1) - 1) else 0)

def birthSpectrumList (m : ℕ) : List (ℕ × ℕ) :=
  (List.range (2 ^ (m - 3))).map fun k => (8 * k + 4, birthSpectrum m k)

def spectrumCheck (m : ℕ) : Bool := birthHistogram m == birthSpectrumList m

/-! ## Floor E: the Zhilina bridge — graph degrees are birth values

Zhilina (IJAC 31, 2021; Part I: DOI 10.1142/S0218196721500326,
Part II: DOI 10.1142/S0218196721500338) studies the "orthogonality graph"
Γ_e(A_{n+1}): its vertices are the lines ±(e_c, s·e_d) of doubly pure basis-pair zero
divisors of A_{m+1} = CD (m+1), and distinct vertices are adjacent iff both
products vanish (Part I, Def. 2.3: "adjacent iff ab = ba = 0"). Her Part II
proves that the special vertices (the ones with a ℓ-component) have degree
2^n − 4 and that the non-special degrees are divisible by 4, without a
per-vertex formula.

The bridge below closes that gap: the lines that annihilate the line
±(e_a, s·e_b) bilaterally are exactly
  (e_r, ±(e_a e_r) e_b),  one line per anti-associating r,
so the degree of every vertex is `birth a b`. The three ingredients:
`ann_two_sided` (a doubly pure product vanishing one way vanishes both
ways, by the conjugation trick), `ann_char` (BDI 11.1: w = (c, σd) is killed
iff c anti-associates and σd = (e_a e_c) e_b), and the sign bookkeeping
`lineSign` (for anti r exactly one σ works). -/

/-- `Same` survives negating the left argument. -/
theorem same_neg_left_iff {m : ℕ} {P : CD m} {u : BUnit m} :
    Same (neg P) (beval u) ↔ Same P (beval u) := by
  constructor
  · intro h
    have h2 := Same.neg_left h
    rw [neg_neg] at h2
    exact h2
  · exact Same.neg_left

/-- A unit is never any unit's negative. -/
theorem beval_ne_neg {m : ℕ} (u v : BUnit m) : beval u ≠ neg (beval v) := by
  intro h
  have huv : u = v := beval_neg_inj m u v h
  rw [← huv] at h
  exact beval_ne_neg_self u h

/-- Sign-literal normalisation (iota on `cond`). -/
theorem cond_true {m : ℕ} (x y : CD m) : cond true x y = x := rfl
theorem cond_false {m : ℕ} (x y : CD m) : cond false x y = y := rfl

/-- The second component of an annihilating line is pinned to `tgt`. -/
theorem cond_eq_unit_unique {m : ℕ} {d u : BUnit m} {s : Bool} {T : CD m}
    (hT : Same T (beval u)) (h : cond s (beval d) (neg (beval d)) = T) : d = u := by
  rcases hT with hT | hT
  · cases s with
    | true =>
      rw [cond_true] at h
      exact beval_inj m d u (h.trans hT)
    | false =>
      rw [cond_false] at h
      have h2 := congrArg neg h
      rw [neg_neg] at h2
      exact absurd (h2.trans (congrArg neg hT)) (beval_ne_neg d u)
  · cases s with
    | true =>
      rw [cond_true, hT] at h
      exact absurd h (beval_ne_neg d u)
    | false =>
      rw [cond_false, hT] at h
      have h2 := congrArg neg h
      rw [neg_neg, neg_neg] at h2
      exact beval_inj m d u h2

/-- The triple product lands on `tgt` up to sign. -/
theorem triple_same_tgt {m : ℕ} (a b r : BUnit m) :
    Same ((beval a * beval r) * beval b) (beval (tgt a b r)) := by
  have h1 := (beval_mul_same a r).mul_right (beval b)
  have h2 := beval_mul_same (bxor a r) b
  have h3 : tgt a b r = bxor (bxor a r) b := by
    show bxor a (bxor r b) = bxor (bxor a r) b
    rw [← bxor_assoc]
  rw [h3]
  exact h1.trans h2

/-- The line ±(e_c, s·e_d) as an element of `CD (m+1)`, first sign fixed. -/
def lineElem {m : ℕ} (c d : BUnit m) (s : Bool) : CD (m + 1) :=
  dbl (beval c) (cond s (beval d) (neg (beval d)))

/-- The line ±(e_c, s·e_d) is annihilated by the line ±(e_a, τ·e_b)
(one-sided by definition; `annLine_bilateral` upgrades to Zhilina's
two-sided adjacency). -/
def annLine {m : ℕ} (a b : BUnit m) (τ : Bool) (c d : BUnit m) (s : Bool) : Prop :=
  lineElem a b τ * lineElem c d s = (cdZero : CD (m + 1))

/-- Signed units keep their conjugation property. -/
theorem conj_cond_self {m : ℕ} {y : CD m} (hy : conj y = neg y) (s : Bool) :
    conj (cond s y (neg y)) = neg (cond s y (neg y)) := by
  cases s with
  | true => exact hy
  | false =>
    rw [cond_false, conj_neg, hy]

/-- Signed units keep their square. -/
theorem sq_cond_self {m : ℕ} {y : CD m} (hy2 : y * y = neg (cdOne : CD m)) (s : Bool) :
    (cond s y (neg y)) * (cond s y (neg y)) = neg (cdOne : CD m) := by
  cases s with
  | true => exact hy2
  | false =>
    rw [cond_false, neg_mul, mul_neg, neg_neg]
    exact hy2

/-- Signed units keep their right alternativity. -/
theorem rart_cond_self {m : ℕ} {y : CD m}
    (hart : ∀ w : CD m, (w * y) * y = w * (y * y)) (s : Bool) (w : CD m) :
    (w * cond s y (neg y)) * cond s y (neg y) = w * (cond s y (neg y) * cond s y (neg y)) := by
  cases s with
  | true => exact hart w
  | false =>
    rw [cond_false]
    have e2 : neg y * neg y = y * y := by rw [neg_mul, mul_neg, neg_neg]
    have e3 : (w * neg y) * neg y = (w * y) * y := by
      rw [mul_neg w y, neg_mul, mul_neg, neg_neg]
    rw [e3, e2, hart w]

theorem conj_lineElem {m : ℕ} {c d : BUnit m} (hc : c ≠ bone m) (s : Bool) :
    conj (lineElem c d s) = neg (lineElem c d s) := by
  show dbl (conj (beval c)) (neg (cond s (beval d) (neg (beval d))))
      = dbl (neg (beval c)) (neg (cond s (beval d) (neg (beval d))))
  rw [conj_beval_of_ne hc]

/-- Doubly pure annihilation is automatically two-sided (conjugation trick). -/
theorem ann_two_sided {m : ℕ} {a b c d : BUnit m} (ha : a ≠ bone m) (hc : c ≠ bone m)
    (τ s : Bool)
    (h : lineElem a b τ * lineElem c d s = (cdZero : CD (m + 1))) :
    lineElem c d s * lineElem a b τ = (cdZero : CD (m + 1)) := by
  have h1 := congrArg conj h
  rw [conj_mul, conj_lineElem ha, conj_lineElem hc, conj_zero,
    neg_mul, mul_neg, neg_neg] at h1
  exact h1

/-- The anti-associator vanishes on a unit iff the triple anti-associates. -/
theorem wa_beval_zero_iff_anti {m : ℕ} (a b c : BUnit m) :
    WA (beval a) (beval b) (beval c) = (cdZero : CD m) ↔ Anti a b c := by
  constructor
  · intro h
    by_contra hna
    rw [WA_beval_of_not_anti hna] at h
    rcases smul_eq_zero.1 h with h2 | h2
    · exact absurd h2 (by norm_num)
    · rcases right_same a b c with hs | hs
      · rw [hs] at h2
        exact beval_ne_zero (tgt a b c) h2
      · rw [hs] at h2
        have h3 := congrArg neg h2
        rw [neg_neg] at h3
        exact beval_ne_zero (tgt a b c) (h3.trans neg_zero)
  · intro h
    exact WA_beval_of_anti h

/-- Flipping the sign of the middle slot flips the anti-associator. -/
theorem wa_neg {m : ℕ} (a b c : BUnit m) :
    WA (beval a) (neg (beval b)) (beval c) = neg (WA (beval a) (beval b) (beval c)) := by
  rw [WA_apply, WA_apply]
  have e1 : (beval a * beval c) * neg (beval b) = neg ((beval a * beval c) * beval b) :=
    mul_neg _ _
  have e2 : beval a * (beval c * neg (beval b)) = neg (beval a * (beval c * beval b)) := by
    rw [mul_neg, mul_neg]
  rw [e1, e2, ← neg_add]

/-- The same, with the annihilator's second slot sign-flipped. -/
theorem wa_cond_zero_iff_anti {m : ℕ} {b : BUnit m} (a c : BUnit m) (τ : Bool) :
    WA (beval a) (cond τ (beval b) (neg (beval b))) (beval c) = (cdZero : CD m) ↔
      Anti a b c := by
  cases τ with
  | true => exact wa_beval_zero_iff_anti a b c
  | false =>
    rw [cond_false]
    constructor
    · intro h
      rw [wa_neg] at h
      have h3 := congrArg neg h
      rw [neg_neg] at h3
      exact (wa_beval_zero_iff_anti a b c).1 (h3.trans neg_zero)
    · intro hA
      have h2 := (wa_beval_zero_iff_anti a b c).2 hA
      rw [wa_neg, congrArg neg h2]
      exact neg_zero

/-- **Characterisation of annihilating lines** (BDI 11.1, unit-pair form):
the line ±(e_c, s·e_d) is killed by ±(e_a, τ·e_b) iff c anti-associates
between a and b and the signed second component equals (e_a e_c)·(τ·e_b). -/
theorem ann_char {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m) (τ : Bool)
    (c d : BUnit m) (s : Bool) :
    lineElem a b τ * lineElem c d s = (cdZero : CD (m + 1)) ↔
      (Anti a b c ∧ cond s (beval d) (neg (beval d))
        = (beval a * beval c) * (cond τ (beval b) (neg (beval b)))) := by
  have key := ker_Lz_iff_ker_W (beval a) (cond τ (beval b) (neg (beval b)))
    (lart a) (rart_cond_self (rart b) τ) (conj_beval_of_ne ha)
    (conj_cond_self (conj_beval_of_ne hb) τ) (sq_beval ha)
    (sq_cond_self (sq_beval hb) τ) (beval c) (cond s (beval d) (neg (beval d)))
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := key.1 h
    rw [← WA_apply] at h2
    exact ⟨(wa_cond_zero_iff_anti a c τ).1 h2, h1⟩
  · rintro ⟨hA, h1⟩
    have h2 := (wa_cond_zero_iff_anti a c τ).2 hA
    rw [WA_apply] at h2
    exact key.2 ⟨h1, h2⟩

/-- τ-normalised form of `ann_char` (vertex sign true). -/
theorem ann_char_true {m : ℕ} {a b c d : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m)
    (s : Bool) :
    lineElem a b true * lineElem c d s = (cdZero : CD (m + 1)) ↔
      (Anti a b c ∧ cond s (beval d) (neg (beval d)) = (beval a * beval c) * beval b) := by
  rw [ann_char ha hb true c d s, cond_true]

/-- τ-normalised form of `ann_char` (vertex sign false). -/
theorem ann_char_false {m : ℕ} {a b c d : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m)
    (s : Bool) :
    lineElem a b false * lineElem c d s = (cdZero : CD (m + 1)) ↔
      (Anti a b c ∧ cond s (beval d) (neg (beval d))
        = (beval a * beval c) * neg (beval b)) := by
  rw [ann_char ha hb false c d s, cond_false]

/-- Flipping the line sign negates the signed second component. -/
theorem cond_not_neg {m : ℕ} (u : BUnit m) (s : Bool) :
    cond (!s) (beval u) (neg (beval u)) = neg (cond s (beval u) (neg (beval u))) := by
  cases s with
  | false =>
    show beval u = neg (neg (beval u))
    exact (neg_neg (beval u)).symm
  | true => rfl

/-- Adjacency against the flipped vertex is adjacency against the vertex
with the flipped line sign. -/
theorem annLine_flip {m : ℕ} {a b c d : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m)
    (s : Bool) :
    annLine a b false c d s ↔ annLine a b true c d (!s) := by
  unfold annLine
  rw [ann_char_false ha hb s, ann_char_true ha hb (!s)]
  constructor
  · rintro ⟨hA, h1⟩
    exact ⟨hA, by rw [cond_not_neg d s, h1, mul_neg, neg_neg]⟩
  · rintro ⟨hA, h1⟩
    refine ⟨hA, ?_⟩
    have h2 := congrArg neg h1
    rw [cond_not_neg d s, neg_neg, ← mul_neg] at h2
    exact h2

open Classical in
/-- The sign that makes the second component match, for anti r. -/
noncomputable def lineSign {m : ℕ} (a b r : BUnit m) : Bool :=
  if (beval a * beval r) * beval b = beval (tgt a b r) then true else false

theorem lineSign_spec {m : ℕ} (a b r : BUnit m) :
    cond (lineSign a b r) (beval (tgt a b r)) (neg (beval (tgt a b r)))
      = (beval a * beval r) * beval b := by
  unfold lineSign
  split
  · next h =>
    rw [cond_true]
    exact h.symm
  · next h =>
    rcases triple_same_tgt a b r with h' | h'
    · exact absurd h' h
    · rw [cond_false]
      exact h'.symm

/-- Membership in `annLine` gives the anti-association. -/
theorem anti_of_annLine {m : ℕ} {a b c d : BUnit m} {s : Bool}
    (ha : a ≠ bone m) (hb : b ≠ bone m) (h : annLine a b true c d s) : Anti a b c :=
  ((ann_char_true ha hb s).1 h).1

/-- Every anti-associating r yields an annihilating line. -/
theorem ann_of_anti {m : ℕ} {a b r : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m)
    (hA : Anti a b r) : annLine a b true r (tgt a b r) (lineSign a b r) :=
  (ann_char_true ha hb (lineSign a b r)).2 ⟨hA, lineSign_spec a b r⟩

/-- For anti c, the annihilating line is unique: `d = tgt` and `s = lineSign`. -/
theorem ann_line_unique {m : ℕ} {a b c d : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m)
    (hab : a ≠ b) (hA : Anti a b c) (s : Bool)
    (h : cond s (beval d) (neg (beval d)) = (beval a * beval c) * beval b) :
    d = tgt a b c ∧ s = lineSign a b c := by
  have hdu : d = tgt a b c := cond_eq_unit_unique (triple_same_tgt a b c) h
  refine ⟨hdu, ?_⟩
  rcases triple_same_tgt a b c with hT | hT
  · have hls : lineSign a b c = true := by
      unfold lineSign
      split
      · rfl
      · next h' => exact absurd hT h'
    cases s with
    | true => exact hls.symm
    | false =>
      rw [cond_false, hdu, hT] at h
      exact absurd h.symm (beval_ne_neg_self (tgt a b c))
  · have hne : ¬((beval a * beval c) * beval b = beval (tgt a b c)) := by
      intro h'
      rw [h'] at hT
      exact beval_ne_neg_self (tgt a b c) hT
    have hls : lineSign a b c = false := by
      unfold lineSign
      split
      · next h' => exact absurd h' hne
      · rfl
    cases s with
    | false => exact hls.symm
    | true =>
      rw [cond_true, hdu, hT] at h
      exact absurd h (beval_ne_neg_self (tgt a b c))

/-- `tgt` has no fixed point when a ≠ b. -/
theorem tgt_ne_self {m : ℕ} (a b c : BUnit m) (hab : a ≠ b) : tgt a b c ≠ c := by
  intro h
  rw [show tgt a b c = bxor a (bxor c b) from rfl] at h
  have h5 := congrArg (fun t => bxor t b) h
  rw [bxor_assoc, bxor_assoc, bxor_self, bxor_bone] at h5
  rw [bxor_comm c b] at h5
  have h6 := congrArg (fun t => bxor t c) h5
  rw [bxor_assoc, bxor_self, bxor_bone, bxor_assoc, bxor_self, bxor_bone] at h6
  exact absurd h6 hab

/-- `tgt` never lands on the quaternion index set. -/
theorem anti_tgt_ne_bone {m : ℕ} {a b c : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m)
    (hab : a ≠ b) (hA : Anti a b c) : tgt a b c ≠ bone m := by
  intro h
  rw [show tgt a b c = bxor a (bxor c b) from rfl] at h
  have h2 : a = bxor c b := bxor_eq_bone_iff.1 h
  have h3 : bxor a b = c := by
    rw [h2, bxor_assoc, bxor_self, bxor_bone]
  exact not_anti_of_mem_Hset ha hb hab (mem_Hset.2 (Or.inr (Or.inr (Or.inr h3.symm)))) hA

/-- Membership in `annLine` automatically gives Zhilina's two-sided adjacency
and the doubly-pure vertex conditions. -/
theorem annLine_bilateral {m : ℕ} {a b c d : BUnit m} {τ s : Bool}
    (ha : a ≠ bone m) (hb : b ≠ bone m) (hab : a ≠ b)
    (h : annLine a b τ c d s) :
    lineElem c d s * lineElem a b τ = (cdZero : CD (m + 1)) ∧ c ≠ bone m ∧ d ≠ bone m
      ∧ c ≠ d := by
  obtain ⟨hA, h1⟩ := (ann_char ha hb τ c d s).1 h
  have hc : c ≠ bone m := fun hcb =>
    not_anti_of_mem_Hset ha hb hab (mem_Hset.2 (Or.inl hcb)) hA
  have hT : Same ((beval a * beval c) * (cond τ (beval b) (neg (beval b))))
      (beval (tgt a b c)) := by
    cases τ with
    | true => exact triple_same_tgt a b c
    | false =>
      rw [cond_false, mul_neg]
      exact same_neg_left_iff.2 (triple_same_tgt a b c)
  have hdu : d = tgt a b c := cond_eq_unit_unique hT h1
  refine ⟨?_, hc, ?_, ?_⟩
  · exact ann_two_sided ha hc τ s h
  · exact fun hdb => anti_tgt_ne_bone ha hb hab hA (hdu.symm.trans hdb)
  · exact fun hcd => tgt_ne_self a b c hab (hcd.trans hdu).symm

/-- No line annihilates itself. -/
theorem lineElem_sq_ne_zero {m : ℕ} {a b : BUnit m} (ha : a ≠ bone m) (hb : b ≠ bone m)
    (hab : a ≠ b) (τ : Bool) : lineElem a b τ * lineElem a b τ ≠ (cdZero : CD (m + 1)) := by
  intro h
  obtain ⟨hA, _⟩ := (ann_char ha hb τ a b τ).1 h
  exact not_anti_of_mem_Hset ha hb hab (mem_Hset.2 (Or.inr (Or.inl rfl))) hA

/-- The parametrisation of lines by triples is injective: same representative,
same triple. -/
theorem line_inj {m : ℕ} {c d c' d' : BUnit m} {s s' : Bool}
    (h : lineElem c d s = lineElem c' d' s') : c = c' ∧ d = d' ∧ s = s' := by
  have h' : (dbl (beval c) (cond s (beval d) (neg (beval d))) : CD (m + 1))
      = dbl (beval c') (cond s' (beval d') (neg (beval d'))) := h
  injection h' with hidx h1 h2
  cases s with
  | true =>
    cases s' with
    | true =>
      rw [cond_true, cond_true] at h2
      exact ⟨beval_inj m c c' h1, beval_inj m d d' h2, rfl⟩
    | false =>
      rw [cond_true, cond_false] at h2
      exact absurd h2 (beval_ne_neg d d')
  | false =>
    cases s' with
    | true =>
      rw [cond_false, cond_true] at h2
      exact absurd h2.symm (beval_ne_neg d' d)
    | false =>
      rw [cond_false, cond_false] at h2
      have h3 := congrArg neg h2
      rw [neg_neg, neg_neg] at h3
      exact ⟨beval_inj m c c' h1, beval_inj m d d' h3, rfl⟩

/-- A line representative is never the negative of another: distinct triples
give distinct lines, with no sign collision. -/
theorem line_ne_neg {m : ℕ} (c d c' d' : BUnit m) (s s' : Bool) :
    lineElem c d s ≠ neg (lineElem c' d' s') := by
  intro h
  have h2 : (neg (lineElem c' d' s') : CD (m + 1))
      = dbl (neg (beval c' : CD m)) (neg (cond s' (beval d') (neg (beval d')))) := rfl
  have h4 : (lineElem c d s : CD (m + 1))
      = dbl (beval c) (cond s (beval d) (neg (beval d))) := rfl
  rw [h2, h4] at h
  injection h with hidx h3 _
  exact beval_ne_neg c c' h3

/-- The anti-associating units are counted by `N`. -/
theorem card_anti_eq_N {m : ℕ} (a b : BUnit m) :
    Fintype.card {r : BUnit m // Anti a b r} = N a b := by
  classical
  rw [Fintype.card_subtype, N_def, Finset.card_eq_sum_ones, ← Finset.sum_filter]

/-- The annihilating lines with vertex sign `true` are counted by `N`. -/
theorem annLines_card_true {m : ℕ} (a b : BUnit m) (ha : a ≠ bone m) (hb : b ≠ bone m)
    (hab : a ≠ b) :
    Fintype.card {p : BUnit m × BUnit m × Bool // annLine a b true p.1 p.2.1 p.2.2}
      = N a b := by
  classical
  have main : {r : BUnit m // Anti a b r} ≃
      {p : BUnit m × BUnit m × Bool // annLine a b true p.1 p.2.1 p.2.2} :=
    { toFun := fun r => ⟨(r.1, tgt a b r.1, lineSign a b r.1), ann_of_anti ha hb r.2⟩
      , invFun := fun p => ⟨p.1.1, anti_of_annLine ha hb p.2⟩
      , left_inv := fun r => Subtype.ext rfl
      , right_inv := fun p => by
          obtain ⟨⟨c, d, s⟩, hp⟩ := p
          obtain ⟨hA, h1⟩ := (ann_char_true ha hb s).1 hp
          obtain ⟨hd, hs⟩ := ann_line_unique ha hb hab hA s h1
          apply Subtype.ext
          show (c, tgt a b c, lineSign a b c) = (c, d, s)
          have hd' : d = tgt a b c := hd
          have hs' : s = lineSign a b c := hs
          rw [hd', hs'] }
  rw [Fintype.card_congr main.symm, card_anti_eq_N a b]

/-- **Zhilina bridge**: in the two-sided zero-divisor graph on doubly pure
basis-pair lines of `CD (m+1)` (Zhilina, orthogonality graph: vertices are
lines of two-sided zero divisors, adjacency iff `ab = ba = 0`; Part II builds
the subgraph Γ_e on unit-pair lines), the degree of the vertex line ±(e_a, τ·e_b)
equals `birth a b`. By `annLine_bilateral` every line counted here is a
genuine two-sided adjacent vertex (doubly pure, distinct components), and by
`lineElem_sq_ne_zero` no vertex is adjacent to itself. This evaluates, per
vertex, the non-special degrees for which Part II proves divisibility by 4
but gives no per-vertex value; the special degree 2^n − 4 of Part II is the
maximum case `birth(c, ℓ)` of the same function. -/
theorem zhilina_degree_eq_birth {m : ℕ} (a b : BUnit m) (ha : a ≠ bone m) (hb : b ≠ bone m)
    (hab : a ≠ b) (τ : Bool) :
    Fintype.card {p : BUnit m × BUnit m × Bool // annLine a b τ p.1 p.2.1 p.2.2}
      = birth a b := by
  classical
  cases τ with
  | true => rw [annLines_card_true a b ha hb hab, N_eq_birth a b ha hb hab]
  | false =>
    have flip : {p : BUnit m × BUnit m × Bool // annLine a b false p.1 p.2.1 p.2.2} ≃
        {p : BUnit m × BUnit m × Bool // annLine a b true p.1 p.2.1 p.2.2} :=
      { toFun := fun p => ⟨(p.1.1, p.1.2.1, !p.1.2.2), (annLine_flip ha hb p.1.2.2).1 p.2⟩
        , invFun := fun p =>
            ⟨(p.1.1, p.1.2.1, !p.1.2.2), by
              exact (annLine_flip ha hb (!p.1.2.2)).2
                (by rw [Bool.not_not]; exact p.2)⟩
        , left_inv := fun p => by
            obtain ⟨⟨c, d, s⟩, hp⟩ := p
            apply Subtype.ext
            simp [Bool.not_not]
        , right_inv := fun p => by
            obtain ⟨⟨c, d, s⟩, hp⟩ := p
            apply Subtype.ext
            simp [Bool.not_not] }
    rw [Fintype.card_congr flip, annLines_card_true a b ha hb hab, N_eq_birth a b ha hb hab]

/-! ## Seal -/

#print axioms finrank_ker_WA_eq_N
#print axioms N_LL
#print axioms N_LU_gen
#print axioms N_LU_bone
#print axioms N_LU_self
#print axioms N_UU_gen
#print axioms N_UU_bone
#print axioms N_eq_birth
#print axioms finrank_ker_WA_birth
#print axioms finrank_ker_WA_birth'
#print axioms birth_props
#print axioms birth_mod_eight
#print axioms finrank_ann_birth
#print axioms exists_annihilator
#print axioms ann_char
#print axioms annLine_flip
#print axioms annLines_card_true
#print axioms zhilina_degree_eq_birth
#print axioms annLine_bilateral
#print axioms lineElem_sq_ne_zero
#print axioms ann_two_sided
#print axioms wa_beval_zero_iff_anti
#print axioms wa_neg
#print axioms wa_cond_zero_iff_anti
#print axioms ann_char_true
#print axioms ann_char_false
#print axioms lineSign_spec
#print axioms ann_line_unique
#print axioms card_anti_eq_N
#print axioms triple_same_tgt
#print axioms cond_eq_unit_unique
#print axioms conj_lineElem
#print axioms tgt_ne_self
#print axioms anti_tgt_ne_bone
#print axioms line_inj
#print axioms line_ne_neg
#print axioms birth_closed
#print axioms birth_four_lifts
#print axioms birthTotal_succ

#eval (List.range 6).map fun k => (k + 3, birthTotal (k + 3), 4 * 8 ^ (k + 2) - 28 * 2 ^ (k + 2) + 24)
#eval (List.range 6).map fun k => (k + 3, spectrumCheck (k + 3))

end Foldlaw
