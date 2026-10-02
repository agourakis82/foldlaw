import Mathlib

/-!
# The Cayley-Dickson fold law: definitions + first targets
Conventions EXACTLY match the C++ code (`tower64.cpp`):
  (x, y) * (a, b) = (x*a - b*conj y, conj x * b + a*y)
  conj (x, y)     = (conj x, -y)
Level 0 = ℝ. `CD n` is an inductive tower so pattern matching reduces.
Targets (claims sheet T12): alternating art; ker L_z ≅ ker W; diagonal
blocks with C = -{L_x, L_y}; H = span{1,x,y,xy} ⊂ ker C; W|_H invertible;
direct sum x•(ker W) ⊓ H = ⊥; FOLD LAW dim ker (d+1) = 2·dim ker d + 4.
-/

namespace Foldlaw

/-- The Cayley-Dickson tower: level 0 is ℝ, each doubling pairs the level below. -/
inductive CD : ℕ → Type
  | zero : ℝ → CD 0
  | dbl : CD n → CD n → CD (n + 1)

open CD

/-- Componentwise negation. -/
def neg : ∀ {m : ℕ}, CD m → CD m
  | 0, zero r => zero (-r)
  | _ + 1, dbl x y => dbl (neg x) (neg y)

/-- Conjugation: trivial at level 0, (x, y)ᶜ = (xᶜ, -y) at each doubling. -/
def conj : ∀ {m : ℕ}, CD m → CD m
  | 0, zero r => zero r
  | _ + 1, dbl x y => dbl (conj x) (neg y)

/-- Componentwise addition (vector space structure). -/
def add : ∀ {m : ℕ}, CD m → CD m → CD m
  | 0, zero r, zero s => zero (r + s)
  | _ + 1, dbl x y, dbl a b => dbl (add x a) (add y b)

/-- Componentwise subtraction. -/
def sub : ∀ {m : ℕ}, CD m → CD m → CD m
  | 0, zero r, zero s => zero (r - s)
  | _ + 1, dbl x y, dbl a b => dbl (sub x a) (sub y b)

/-- CD multiplication (code convention): (x,y)*(a,b) = (x*a - b*yᶜ, xᶜ*b + a*y). -/
def mul : ∀ {m : ℕ}, CD m → CD m → CD m
  | 0, zero r, zero s => zero (r * s)
  | _ + 1, dbl x y, dbl a b =>
      dbl (sub (mul x a) (mul b (conj y))) (add (mul (conj x) b) (mul a y))

instance : Add (CD m) := ⟨add⟩
instance : Neg (CD m) := ⟨neg⟩
instance : Sub (CD m) := ⟨sub⟩
instance : HMul (CD m) (CD m) (CD m) := ⟨mul⟩

-- NOTE (honest scope): alternating art FAILS at levels >= 4 (sedenions are
-- not alternative). art_left / art_right as tower-wide statements are FALSE.
-- Correct reduction: associativity at level m implies art at level m+1.
-- Claims sheet: "H subset ker C by alternating art" closes for the tested
-- base pairs (check G: 930/930; there conj x * x = 1), not as a general law.

/- Target T1' (left art, honest form). NOTE (2026-10-01): associativity
alone is NOT enough -- expanding the successor step, the components reduce to
identities requiring the norm a * conj a and trace a + conj a to be CENTRAL
at level m (quadratic algebra, Schafer). These hold at levels 0-2 (R, C, H),
giving alternativity at level 3 (O) -- and failing beyond, where the art
indeed dies. The theorem itself lives near the end of the file, after the
lemmas its proof consumes (Lean needs no forward references). Same for T2'
(right art, honest form): same quadratic hypotheses. -/

/-- Double negation at every level. -/
theorem neg_neg {m : ℕ} (a : CD m) : neg (neg a) = a := by
  induction m with
  | zero => cases a; simp [neg]
  | succ n ih =>
    cases a with
    | dbl x y => simp [neg, ih]

/-- Conjugation is an involution at every level (needed everywhere in the
art expansion; base lemma of the fold-law chain). -/
theorem conj_conj {m : ℕ} (a : CD m) : conj (conj a) = a := by
  induction m with
  | zero => cases a; rfl
  | succ n ih =>
    cases a with
    | dbl x y => simp [conj, ih, neg_neg]

theorem add_comm {m : ℕ} (a b : CD m) : a + b = b + a := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => exact congrArg zero (_root_.add_comm r s)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v => exact congrArg₂ dbl (ih x u) (ih y v)

theorem add_assoc {m : ℕ} (a b c : CD m) : a + b + c = a + (b + c) := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        cases c with
        | zero t => exact congrArg zero (_root_.add_assoc r s t)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v =>
        cases c with
        | dbl p q => exact congrArg₂ dbl (ih x u p) (ih y v q)

theorem neg_add {m : ℕ} (a b : CD m) : neg (a + b) = neg a + neg b := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => exact congrArg zero (_root_.neg_add r s)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v => exact congrArg₂ dbl (ih x u) (ih y v)

theorem conj_add {m : ℕ} (a b : CD m) : conj (a + b) = conj a + conj b := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => rfl
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v => exact congrArg₂ dbl (ih x u) (neg_add y v)

theorem sub_add {m : ℕ} (a b : CD m) : a - b = a + neg b := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => exact congrArg zero (_root_.sub_eq_add_neg r s)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v => exact congrArg₂ dbl (ih x u) (ih y v)

theorem sub_dist {m : ℕ} (a b c d : CD m) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        cases c with
        | zero t =>
          cases d with
          | zero w =>
            exact congrArg zero (show (r + s) - (t + w) = (r - t) + (s - w) by ring)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v =>
        cases c with
        | dbl p q =>
          cases d with
          | dbl w z =>
            exact congrArg₂ dbl (ih x u p w) (ih y v q z)

theorem add_four {m : ℕ} (P Q R S : CD m) :
    (P + Q) + (R + S) = (P + R) + (Q + S) := by
  rw [← add_assoc (P + Q) R S, add_assoc P Q R, add_comm Q R,
    add_assoc P (R + Q) S, add_assoc R Q S, ← add_assoc P R (Q + S)]

/-- Both distributivity laws, proved together (each uses the other in the
successor step). -/
theorem distrib {m : ℕ} (a b c : CD m) :
    a * (b + c) = a * b + a * c ∧ (b + c) * a = b * a + c * a := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        cases c with
        | zero t =>
          constructor
          · exact congrArg zero (show r * (s + t) = r * s + r * t by ring)
          · exact congrArg zero (show (s + t) * r = s * r + t * r by ring)
  | succ n ih =>
    cases a with
    | dbl a1 a2 =>
      cases b with
      | dbl b1 b2 =>
cases c with
    | dbl c1 c2 =>
      have hL : ∀ a b c : CD n, a * (b + c) = a * b + a * c :=
        fun a b c => (ih a b c).1
      have hR : ∀ a b c : CD n, (b + c) * a = b * a + c * a :=
        fun a b c => (ih a b c).2
      have h1 : a1 * (b1 + c1) - (b2 + c2) * conj a2
          = (a1 * b1 - b2 * conj a2) + (a1 * c1 - c2 * conj a2) := by
        rw [hL a1 b1 c1, hR (conj a2) b2 c2, sub_dist]
      have h2 : conj a1 * (b2 + c2) + (b1 + c1) * a2
          = (conj a1 * b2 + b1 * a2) + (conj a1 * c2 + c1 * a2) := by
        rw [hL (conj a1) b2 c2, hR a2 b1 c1, add_four]
      have h3 : (b1 + c1) * a1 - a2 * conj (b2 + c2)
          = (b1 * a1 - a2 * conj b2) + (c1 * a1 - a2 * conj c2) := by
        rw [hR a1 b1 c1, conj_add b2 c2, hL a2 (conj b2) (conj c2), sub_dist]
      have h4 : conj (b1 + c1) * a2 + a1 * (b2 + c2)
          = (conj b1 * a2 + a1 * b2) + (conj c1 * a2 + a1 * c2) := by
        rw [conj_add b1 c1, hR a2 (conj b1) (conj c1), hL a1 b2 c2, add_four]
      constructor
      · exact congrArg₂ dbl h1 h2
      · exact congrArg₂ dbl h3 h4

theorem conj_neg {m : ℕ} (a : CD m) : conj (neg a) = neg (conj a) := by
  induction m with
  | zero => cases a with
    | zero r => rfl
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) rfl

/-- neg_mul and mul_neg proved together: each uses the other in the
successor step. -/
theorem neg_mul_mul_neg {m : ℕ} (a b : CD m) :
    neg a * b = neg (a * b) ∧ a * neg b = neg (a * b) := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        constructor
        · exact congrArg zero (show -r * s = -(r * s) by ring)
        · exact congrArg zero (show r * -s = -(r * s) by ring)
  | succ n ih =>
    have hN : ∀ a b : CD n, neg a * b = neg (a * b) := fun a b => (ih a b).1
    have hM : ∀ a b : CD n, a * neg b = neg (a * b) := fun a b => (ih a b).2
    cases a with
    | dbl a1 a2 =>
      cases b with
      | dbl b1 b2 =>
        have h1 : neg a1 * b1 - b2 * conj (neg a2)
            = neg (a1 * b1 - b2 * conj a2) := by
          rw [hN a1 b1, conj_neg a2, hM b2 (conj a2), sub_add, sub_add,
            neg_add, neg_neg (b2 * conj a2)]
        have h2 : conj (neg a1) * b2 + b1 * neg a2
            = neg (conj a1 * b2 + b1 * a2) := by
          rw [conj_neg a1, hN (conj a1) b2, hM b1 a2, neg_add]
        have h3 : a1 * neg b1 - neg b2 * conj a2
            = neg (a1 * b1 - b2 * conj a2) := by
          rw [hM a1 b1, hN b2 (conj a2), sub_add, sub_add,
            neg_add, neg_neg (b2 * conj a2)]
        have h4 : conj a1 * neg b2 + neg b1 * a2
            = neg (conj a1 * b2 + b1 * a2) := by
          rw [hM (conj a1) b2, hN b1 a2, neg_add]
        constructor
        · exact congrArg₂ dbl h1 h2
        · exact congrArg₂ dbl h3 h4

theorem neg_mul {m : ℕ} (a b : CD m) : neg a * b = neg (a * b) :=
  (neg_mul_mul_neg a b).1

theorem mul_neg {m : ℕ} (a b : CD m) : a * neg b = neg (a * b) :=
  (neg_mul_mul_neg a b).2

/-- Conjugation is an anti-automorphism: conj (a * b) = conj b * conj a. -/
theorem conj_mul {m : ℕ} (a b : CD m) : conj (a * b) = conj b * conj a := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s => exact congrArg zero (show r * s = s * r by ring)
  | succ n ih =>
    cases a with
    | dbl a1 a2 =>
      cases b with
      | dbl b1 b2 =>
        have h1 : conj (a1 * b1 - b2 * conj a2)
            = conj b1 * conj a1 - neg a2 * conj (neg b2) := by
          rw [sub_add, conj_add, conj_neg (b2 * conj a2), ih a1 b1,
            ih b2 (conj a2), conj_conj a2, conj_neg b2,
            neg_mul a2 (neg (conj b2)), mul_neg a2 (conj b2),
            neg_neg (a2 * conj b2), sub_add]
        have h2 : neg (conj a1 * b2 + b1 * a2)
            = conj (conj b1) * neg a2 + conj a1 * neg b2 := by
          rw [neg_add, conj_conj b1, mul_neg b1 a2, mul_neg (conj a1) b2,
            add_comm (neg (conj a1 * b2)) (neg (b1 * a2))]
        exact congrArg₂ dbl h1 h2

/-- The three quadratic hypotheses at level 0 (R): trivial, but these are
the base cases of the induction chain R -> C -> H that yields art at O. -/
theorem hassoc_zero (a b c : CD 0) : a * b * c = a * (b * c) := by
  cases a with
  | zero x =>
    cases b with
    | zero y =>
      cases c with
      | zero z =>
        exact congrArg zero (show x * y * z = x * (y * z) by ring)

theorem trace_central_zero (r c : CD 0) : (r + conj r) * c = c * (r + conj r) := by
  cases r with
  | zero x =>
    cases c with
    | zero y =>
      exact congrArg zero (show (x + x) * y = y * (x + x) by ring)

theorem norm_central_zero (r c : CD 0) : (r * conj r) * c = c * (r * conj r) := by
  cases r with
  | zero x =>
    cases c with
    | zero y =>
      exact congrArg zero (show (x * x) * y = y * (x * x) by ring)

/-- The zero of the tower (base of the identity-lemma block needed for the
hereditary step: conj_zero, zero_mul, mul_zero, add_zero, sub_self...). -/
def cdZero : ∀ {m : ℕ}, CD m
  | 0 => zero 0
  | _ + 1 => dbl cdZero cdZero

/-- The one of the tower: (1, 0, 0, ...) at every level. -/
def cdOne : ∀ {m : ℕ}, CD m
  | 0 => zero 1
  | _ + 1 => dbl cdOne cdZero

theorem neg_zero {m : ℕ} : neg (cdZero : CD m) = cdZero := by
  induction m with
  | zero => exact congrArg zero _root_.neg_zero
  | succ n ih => exact congrArg₂ dbl ih ih

theorem conj_zero {m : ℕ} : conj (cdZero : CD m) = cdZero := by
  induction m with
  | zero => rfl
  | succ n ih => exact congrArg₂ dbl ih neg_zero

theorem add_zero {m : ℕ} (a : CD m) : a + cdZero = a := by
  induction m with
  | zero =>
    cases a with
    | zero r => exact congrArg zero (_root_.add_zero r)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem zero_add {m : ℕ} (a : CD m) : cdZero + a = a := by
  induction m with
  | zero =>
    cases a with
    | zero r => exact congrArg zero (_root_.zero_add r)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem add_neg_self {m : ℕ} (a : CD m) : a + neg a = cdZero := by
  induction m with
  | zero =>
    cases a with
    | zero r => exact congrArg zero (show r + -r = (0:ℝ) by ring)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem sub_self {m : ℕ} (a : CD m) : a - a = cdZero := by
  rw [sub_add, add_neg_self]

theorem zero_mul_mul_zero {m : ℕ} (a b : CD m) :
    (cdZero : CD m) * b = cdZero ∧ a * (cdZero : CD m) = cdZero := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        constructor
        · exact congrArg zero (show (0:ℝ) * s = 0 by ring)
        · exact congrArg zero (show r * (0:ℝ) = 0 by ring)
  | succ n ih =>
    have hZ : ∀ b : CD n, cdZero * b = cdZero := fun b => (ih cdZero b).1
    have hM : ∀ a : CD n, a * cdZero = cdZero := fun a => (ih a cdZero).2
    cases a with
    | dbl p q =>
      cases b with
      | dbl u v =>
        have c1 : (cdZero : CD n) * u - v * conj (cdZero : CD n) = cdZero := by
          rw [hZ u, conj_zero, hM v, sub_self]
        have c2 : conj (cdZero : CD n) * v + u * (cdZero : CD n) = cdZero := by
          rw [conj_zero, hZ v, hM u, add_zero]
        have c3 : p * (cdZero : CD n) - (cdZero : CD n) * conj q = cdZero := by
          rw [hM p, hZ (conj q), sub_self]
        have c4 : conj p * (cdZero : CD n) + (cdZero : CD n) * q = cdZero := by
          rw [hM (conj p), hZ q, add_zero]
        constructor
        · exact congrArg₂ dbl c1 c2
        · exact congrArg₂ dbl c3 c4

theorem zero_mul {m : ℕ} (b : CD m) : (cdZero : CD m) * b = cdZero :=
  (zero_mul_mul_zero cdZero b).1

theorem mul_zero {m : ℕ} (a : CD m) : a * (cdZero : CD m) = cdZero :=
  (zero_mul_mul_zero a cdZero).2

theorem conj_one {m : ℕ} : conj (cdOne : CD m) = cdOne := by
  induction m with
  | zero => rfl
  | succ n ih => exact congrArg₂ dbl ih neg_zero

theorem sub_zero {m : ℕ} (a : CD m) : a - (cdZero : CD m) = a := by
  rw [sub_add, neg_zero, add_zero]

theorem one_mul_mul_one {m : ℕ} (a b : CD m) :
    (cdOne : CD m) * b = b ∧ a * (cdOne : CD m) = a := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      cases b with
      | zero s =>
        constructor
        · exact congrArg zero (show (1:ℝ) * s = s by ring)
        · exact congrArg zero (show r * (1:ℝ) = r by ring)
  | succ n ih =>
    have h1 : ∀ b : CD n, (cdOne : CD n) * b = b := fun b => (ih cdOne b).1
    have h2 : ∀ a : CD n, a * (cdOne : CD n) = a := fun a => (ih a cdOne).2
    cases a with
    | dbl p q =>
      cases b with
      | dbl u v =>
        have c1 : (cdOne : CD n) * u - v * conj (cdZero : CD n) = u := by
          rw [h1 u, conj_zero, mul_zero, sub_zero]
        have c2 : conj (cdOne : CD n) * v + u * (cdZero : CD n) = v := by
          rw [conj_one, h1 v, mul_zero, add_zero]
        have c3 : p * (cdOne : CD n) - (cdZero : CD n) * conj q = p := by
          rw [h2 p, zero_mul, sub_zero]
        have c4 : conj p * (cdZero : CD n) + (cdOne : CD n) * q = q := by
          rw [mul_zero, h1 q, zero_add]
        constructor
        · exact congrArg₂ dbl c1 c2
        · exact congrArg₂ dbl c3 c4

theorem one_mul {m : ℕ} (b : CD m) : (cdOne : CD m) * b = b :=
  (one_mul_mul_one cdOne b).1

theorem mul_one {m : ℕ} (a : CD m) : a * (cdOne : CD m) = a :=
  (one_mul_mul_one a cdOne).2

/-- The central-pair bridge: an element (t, cdZero) with t fixed by
conjugation and central at level m commutes with EVERYTHING at level m+1.
This is the norm-to-centrality bridge the hereditary step consumes. -/
theorem real_pair_central {m : ℕ} (t u v : CD m)
    (hfix : conj t = t) (hcomm : ∀ c : CD m, t * c = c * t) :
    dbl t (cdZero : CD m) * dbl u v = dbl u v * dbl t (cdZero : CD m) := by
  have h1 : t * u - v * conj (cdZero : CD m)
      = u * t - (cdZero : CD m) * conj v := by
    rw [conj_zero, mul_zero, sub_zero, hcomm u, zero_mul, sub_zero]
  have h2 : conj t * v + u * (cdZero : CD m)
      = conj u * (cdZero : CD m) + t * v := by
    rw [hfix, mul_zero, add_zero, mul_zero, zero_add]
  exact congrArg₂ dbl h1 h2

/-- Hereditary step for the trace: if a + conj a is central at level m,
then x + conj x is central at level m+1 (every trace is a real pair
(t, cdZero), which real_pair_central makes commute with everything). -/
theorem trace_central_succ {m : ℕ}
    (htrace : ∀ a c : CD m, (a + conj a) * c = c * (a + conj a))
    (x c : CD (m + 1)) : (x + conj x) * c = c * (x + conj x) := by
  cases x with
  | dbl p q =>
    cases c with
    | dbl u v =>
      show dbl (p + conj p) (q + neg q) * dbl u v
        = dbl u v * dbl (p + conj p) (q + neg q)
      rw [add_neg_self]
      exact real_pair_central (p + conj p) u v
        (by rw [conj_add, conj_conj, add_comm]) (htrace p)

theorem neg_add_self {m : ℕ} (a : CD m) : neg a + a = cdZero := by
  rw [add_comm, add_neg_self]

theorem mul_add' {m : ℕ} (a b c : CD m) : a * (b + c) = a * b + a * c :=
  (distrib a b c).1

theorem add_mul' {m : ℕ} (a b c : CD m) : (b + c) * a = b * a + c * a :=
  (distrib a b c).2

theorem central_add {m : ℕ} (t s : CD m)
    (ht : ∀ c : CD m, t * c = c * t) (hs : ∀ c : CD m, s * c = c * s) :
    ∀ c : CD m, (t + s) * c = c * (t + s) := by
  intro c
  rw [add_mul', mul_add', ht c, hs c]

/-- Hereditary step for the norm: if a * conj a is central at level m,
then x * conj x is central at level m+1 (the norm is the real pair
(p * conj p + q * conj q, cdZero), central as a sum of central elements). -/
theorem norm_central_succ {m : ℕ}
    (hnorm : ∀ a c : CD m, (a * conj a) * c = c * (a * conj a))
    (x c : CD (m + 1)) : (x * conj x) * c = c * (x * conj x) := by
  cases x with
  | dbl p q =>
    cases c with
    | dbl u v =>
      show dbl (p * conj p - neg q * conj q) (conj p * neg q + conj p * q)
          * dbl u v
        = dbl u v * dbl (p * conj p - neg q * conj q) (conj p * neg q + conj p * q)
      rw [neg_mul, sub_add, neg_neg, mul_neg, neg_add_self]
      exact real_pair_central (p * conj p + q * conj q) u v
        (by rw [conj_add, conj_mul q (conj q), conj_mul p (conj p), conj_conj q,
            conj_conj p, add_comm])
        (central_add (p * conj p) (q * conj q) (hnorm p) (hnorm q))

theorem comm_zero (a b : CD 0) : a * b = b * a := by
  cases a with
  | zero r =>
    cases b with
    | zero s => exact congrArg zero (show r * s = s * r by ring)

/-- Conjugation distributes over subtraction. -/
theorem conj_sub {m : ℕ} (a b : CD m) : conj (a - b) = conj a - conj b := by
  rw [sub_add, conj_add, conj_neg, ← sub_add]

/-- Left distribution of subtraction over multiplication. -/
theorem sub_mul {m : ℕ} (a b c : CD m) : (a - b) * c = a * c - b * c := by
  rw [sub_add, add_mul', neg_mul, ← sub_add]

/-- Right distribution of subtraction over multiplication. -/
theorem mul_sub {m : ℕ} (a b c : CD m) : a * (b - c) = a * b - a * c := by
  rw [sub_add, mul_add', mul_neg, ← sub_add]

/-- Additive shuffle consumed by the C1 alignment of `assoc_succ_of_comm`. -/
theorem sub_sub_add_shuffle {m : ℕ} (A B C D : CD m) :
    (A - B) - (C + D) = (A - C) - (D + B) := by
  rw [sub_add (A - B) (C + D), sub_add A B, sub_add (A - C) (D + B), sub_add A C,
      neg_add C D, neg_add D B, add_four A (neg B) (neg C) (neg D),
      add_comm (neg B) (neg D)]

/-- Additive shuffle consumed by the C2 alignment of `assoc_succ_of_comm`. -/
theorem sub_add_add_shuffle {m : ℕ} (A B C D : CD m) :
    (A - D) + (B + C) = (A + B) + (C - D) := by
  rw [sub_add A D, sub_add C D, add_four A (neg D) B C, add_comm (neg D) C]

/-- Left cancellation in the additive group (base of the norm-flip argument:
from (a + ā) * a = a * (a + ā) cancel a * a and get ā * a = a * ā). -/
theorem add_left_cancel' {m : ℕ} {A B C : CD m} (h : A + B = A + C) : B = C := by
  have h1 : neg A + (A + B) = neg A + (A + C) := congrArg (fun t => neg A + t) h
  rw [← add_assoc, neg_add_self, zero_add, ← add_assoc, neg_add_self, zero_add] at h1
  exact h1

/-- Right rotation of a 3-sum: A + (B + C) = C + (A + B). -/
theorem add_rot3 {m : ℕ} (A B C : CD m) : A + (B + C) = C + (A + B) := by
  rw [← add_assoc A B C, add_comm (A + B) C]

/-- Structural shuffle consumed by C1 of `art_left_of_assoc`: with Z = W and
X + Y = R + S, the nested difference aligns with the grouped difference. -/
theorem art_sub_shuffle {m : ℕ} (P X Y Z W R S : CD m)
    (h1 : Z = W) (h2 : X + Y = R + S) :
    (P - X) - (Y + Z) = (P - W) - (R + S) := by
  rw [h1, ← h2,
      sub_add (P - X) (Y + W), sub_add P X, neg_add Y W,
      add_assoc P (neg X) (neg Y + neg W),
      sub_add (P - W) (X + Y), sub_add P W, neg_add X Y,
      add_assoc P (neg W) (neg X + neg Y),
      add_rot3 (neg X) (neg Y) (neg W)]

/-- Structural shuffle consumed by C2 of `art_left_of_assoc`. -/
theorem art_pair_shuffle {m : ℕ} (A B C D E F G : CD m)
    (h1 : D = E) (h2 : B + C = F + G) :
    (A + B) + (C - D) = (A - E) + (F + G) := by
  rw [h1, sub_add C E, add_assoc A B (C + neg E), ← add_assoc B C (neg E), h2,
      sub_add A E, add_assoc A (neg E) (F + G), add_comm (F + G) (neg E)]

/-- Target: associativity lifts from a COMMUTATIVE associative level to the
next level. NOTE (2026-10-01, paper check): associativity alone does NOT lift
-- H -> O is the counterexample (H associative, O not) -- commutativity at
level m is required. Hence R (comm+assoc) -> C (assoc) -> H (assoc), and the
chain stops exactly where the art stops.

PROOF MAP (paper, 2026-10-01): with x = (p,q), y = (u,v), z = (w,s),
both sides reduce to 4-term sums; align term by term via hC then hA:
  C1: (p*u - v*qbar)*w - s*(vbar*p + qbar*ubar)  vs
      p*(u*w - s*vbar) - (ubar*s + w*v)*qbar
    - p*u*w  =  p*u*w  (identical)
    - v*qbar*w  =  w*v*qbar  : (w*v)=(v*w) [hC], (v*w)*qbar = v*(w*qbar) [hA],
      w*qbar = qbar*w [hC], v*(qbar*w) = (v*qbar)*w [hA]
    - s*vbar*p  =  p*s*vbar  : (s*vbar)*p = p*(s*vbar) [hC] = (p*s)*vbar [hA]
    - s*qbar*ubar  =  ubar*s*qbar  : (s*qbar)*ubar = ubar*(s*qbar) [hC]
      = (ubar*s)*qbar [hA]
  C2: (ubar*pbar - q*vbar)*s + w*(pbar*v + u*q)  vs
      pbar*(ubar*s + w*v) + (u*w - s*vbar)*q
    same dance: extract with sub_add/add_mul'/mul_add'/neg_mul, align with
    hC-then-hA, close with sub_zero/add_zero.
Tactic pattern: split each side into named 4-term haves, rewrite with
EXPLICIT instances (rw with metavars rewrites first match only).
Instantiation: comm_zero + hassoc_zero give m=0 (C associative); m=1 (H). -/
theorem assoc_succ_of_comm {m : ℕ}
    (hA : ∀ a b c : CD m, a * b * c = a * (b * c))
    (hC : ∀ a b : CD m, a * b = b * a)
    (x y z : CD (m + 1)) : x * y * z = x * (y * z) := by
  cases x with
  | dbl p q =>
    cases y with
    | dbl u v =>
      cases z with
      | dbl w s =>
        -- C1: first components. Normalize conj on both sides, expand the
        -- products, then align term by term hC-then-hA exactly as in the map.
        have hC1 : (p * u - v * conj q) * w - s * conj (conj p * v + u * q)
            = p * (u * w - s * conj v) - (conj u * s + w * v) * conj q := by
          rw [conj_add (conj p * v) (u * q), conj_mul (conj p) v, conj_mul u q,
              conj_conj p,
              sub_mul (p * u) (v * conj q) w,
              mul_add' s (conj v * p) (conj q * conj u),
              ← hA s (conj v) p, ← hA s (conj q) (conj u),
              mul_sub p (u * w) (s * conj v),
              ← hA p u w, ← hA p s (conj v),
              add_mul' (conj q) (conj u * s) (w * v),
              hA v (conj q) w, hC (conj q) w, ← hA v w (conj q), hC v w,
              hC (s * conj v) p, ← hA p s (conj v),
              hC (s * conj q) (conj u), ← hA (conj u) s (conj q),
              sub_sub_add_shuffle (p * u * w) (w * v * conj q)
                (p * s * conj v) (conj u * s * conj q)]
        -- C2: second components. Same dance: conj-normalize, expand, align.
        have hC2 : conj (p * u - v * conj q) * s + w * (conj p * v + u * q)
            = conj p * (conj u * s + w * v) + (u * w - s * conj v) * q := by
          rw [conj_sub (p * u) (v * conj q), conj_mul p u, conj_mul v (conj q),
              conj_conj q,
              sub_mul (conj u * conj p) (q * conj v) s,
              mul_add' w (conj p * v) (u * q),
              ← hA w (conj p) v, ← hA w u q,
              mul_add' (conj p) (conj u * s) (w * v),
              ← hA (conj p) (conj u) s, ← hA (conj p) w v,
              sub_mul (u * w) (s * conj v) q,
              hC (conj u) (conj p),
              hC (q * conj v) s, hC q (conj v), ← hA s (conj v) q,
              hC w (conj p), hC w u,
              sub_add_add_shuffle (conj p * conj u * s) (conj p * w * v)
                (u * w * q) (s * conj v * q)]
        exact congrArg₂ dbl hC1 hC2

/-- Instantiation m=0: ℂ (CD 1) is associative, from ℝ commutative+associative. -/
theorem assoc_one (x y z : CD 1) : x * y * z = x * (y * z) :=
  assoc_succ_of_comm hassoc_zero comm_zero x y z

/-- ℂ is commutative: at level 0 conjugation is the identity, so both
components reduce to commutativity of ℝ. This is the last rung where
commutativity holds -- ℍ kills it, and the chain stops with the art. -/
theorem comm_one (x y : CD 1) : x * y = y * x := by
  have hconj : ∀ t : CD 0, conj t = t := fun t => by cases t with | zero r => rfl
  cases x with
  | dbl a b =>
    cases y with
    | dbl c d =>
      have k1 : a * c - d * conj b = c * a - b * conj d := by
        rw [hconj b, hconj d, comm_zero a c, comm_zero d b]
      have k2 : conj a * d + c * b = conj c * b + a * d := by
        rw [hconj a, hconj c, add_comm (a * d) (c * b)]
      exact congrArg₂ dbl k1 k2

/-- Instantiation m=1: ℍ (CD 2) is associative. -/
theorem assoc_two (x y z : CD 2) : x * y * z = x * (y * z) :=
  assoc_succ_of_comm assoc_one comm_one x y z

/-!
### The honest art (T1'/T2')

Associativity at level m does NOT lift to the double (H → O is the
counterexample); what lifts, given a QUADRATIC level m (trace and norm
central, Schafer), is the art. Expansion with x = (p,q), w = (u,v) and the
code convention (x,y)*(a,b) = (x*a - b*ȳ, x̄*b + a*y):

  C1: p*(p*u - v*q̄) - (p̄*v + u*q)*q̄ = (p*p - q*q̄)*u - v*(q̄*p + q̄*p̄)
      - p*p*u identical on both sides;
      - p*v*q̄ + p̄*v*q̄ = (p + p̄)*v*q̄ = (v*q̄)*(p + p̄) = v*q̄*p + v*q̄*p̄
        (reassociate, then TRACE centrality `htrace p`);
      - u*q*q̄ = u*(q*q̄) = (q*q̄)*u (NORM centrality `hnorm q`).
  C2: p̄*(p̄*v + u*q) + (p*u - v*q̄)*q = (p̄*p̄ - q*q̄)*v + u*(p̄*q + p*q)
      - p̄*p̄*v identical;
      - p̄*(u*q) + p*(u*q) = (p̄ + p)*(u*q) = (u*(p̄ + p))*q = u*p̄*q + u*p*q
        (flipped trace centrality, from `htrace (conj p)` via conj_conj);
      - v*q̄*q = v*(q̄*q) = v*(q*q̄) = (q*q̄)*v (norm flip q̄*q = q*q̄ first,
        itself derived from `htrace` by additive cancellation).
-/

/-- Target T1' (left art, honest form): a quadratic associative level m
(central trace and norm) doubles into a left-alternative level m+1. -/
theorem art_left_of_assoc {m : ℕ}
    (hassoc : ∀ a b c : CD m, a * b * c = a * (b * c))
    (htrace : ∀ a c : CD m, (a + conj a) * c = c * (a + conj a))
    (hnorm : ∀ a c : CD m, a * conj a * c = c * (a * conj a))
    (x w : CD (m + 1)) : x * (x * w) = (x * x) * w := by
  -- Norm flip: ā * a = a * ā, by cancelling a * a from the trace law on a.
  have hnormflip : ∀ a : CD m, conj a * a = a * conj a := by
    intro a
    have h : (a + conj a) * a = a * (a + conj a) := htrace a a
    rw [add_mul', mul_add'] at h
    exact add_left_cancel' h
  cases x with
  | dbl p q =>
    cases w with
    | dbl u v =>
      -- The flipped trace conj p + p is central: htrace (conj p) + conj_conj.
      have hpivot : ∀ c : CD m, (conj p + p) * c = c * (conj p + p) := by
        intro c
        have h := htrace (conj p) c
        rw [conj_conj p] at h
        exact h
      -- C1 pivots.
      have tpiv : (p + conj p) * v * conj q = v * conj q * (p + conj p) := by
        rw [hassoc (p + conj p) v (conj q), htrace p (v * conj q)]
      have npiv : u * q * conj q = q * conj q * u := by
        rw [hassoc u q (conj q), ← hnorm q u]
      have Lgrp : p * v * conj q + conj p * v * conj q
          = (p + conj p) * v * conj q := by
        rw [← add_mul' (conj q) (p * v) (conj p * v), ← add_mul' v p (conj p)]
      have Rgrp : v * conj q * p + v * conj q * conj p
          = v * conj q * (p + conj p) := by
        rw [← mul_add' (v * conj q) p (conj p)]
      have mid1 : p * v * conj q + conj p * v * conj q
          = v * conj q * p + v * conj q * conj p := by
        rw [Lgrp, tpiv, Rgrp]
      -- C2 pivots.
      have tpiv2 : (conj p + p) * (u * q) = (u * (conj p + p)) * q := by
        rw [← hassoc (conj p + p) u q, hpivot u]
      have npiv2 : v * conj q * q = q * conj q * v := by
        rw [hassoc v (conj q) q, hnormflip q, ← hnorm q v]
      have mid2 : conj p * (u * q) + p * (u * q)
          = u * conj p * q + u * p * q := by
        rw [← add_mul' (u * q) (conj p) p, tpiv2,
            ← add_mul' q (u * conj p) (u * p), ← mul_add' u (conj p) p]
      -- Component equalities, stated EXACTLY as the definitional expansion
      -- of the goal components so `congrArg₂ dbl` applies.
      have k1 : p * (p * u - v * conj q) - (conj p * v + u * q) * conj q
          = (p * p - q * conj q) * u - v * conj (conj p * q + p * q) := by
        rw [conj_add (conj p * q) (p * q), conj_mul (conj p) q, conj_mul p q,
            conj_conj p,
            mul_sub p (p * u) (v * conj q),
            ← hassoc p p u, ← hassoc p v (conj q),
            add_mul' (conj q) (conj p * v) (u * q),
            sub_mul (p * p) (q * conj q) u,
            mul_add' v (conj q * p) (conj q * conj p),
            ← hassoc v (conj q) p, ← hassoc v (conj q) (conj p),
            art_sub_shuffle (p * p * u) (p * v * conj q) (conj p * v * conj q)
              (u * q * conj q) (q * conj q * u) (v * conj q * p)
              (v * conj q * conj p) npiv mid1]
      have k2 : conj p * (conj p * v + u * q) + (p * u - v * conj q) * q
          = conj (p * p - q * conj q) * v + u * (conj p * q + p * q) := by
        rw [conj_sub (p * p) (q * conj q), conj_mul p p, conj_mul q (conj q),
            conj_conj q,
            mul_add' (conj p) (conj p * v) (u * q), ← hassoc (conj p) (conj p) v,
            sub_mul (p * u) (v * conj q) q, hassoc p u q,
            sub_mul (conj p * conj p) (q * conj q) v,
            mul_add' u (conj p * q) (p * q), ← hassoc u (conj p) q,
            ← hassoc u p q,
            art_pair_shuffle (conj p * conj p * v) (conj p * (u * q))
              (p * (u * q)) (v * conj q * q) (q * conj q * v) (u * conj p * q)
              (u * p * q) npiv2 mid2]
      exact congrArg₂ dbl k1 k2

/-- Target T2' (right art, honest form): mirror of the left art, obtained by
conjugating the goal and applying the left art at the conjugates. -/
theorem art_right_of_assoc {m : ℕ}
    (hassoc : ∀ a b c : CD m, a * b * c = a * (b * c))
    (htrace : ∀ a c : CD m, (a + conj a) * c = c * (a + conj a))
    (hnorm : ∀ a c : CD m, a * conj a * c = c * (a * conj a))
    (w x : CD (m + 1)) : (w * x) * x = w * (x * x) := by
  rw [← conj_conj ((w * x) * x),
      conj_mul (w * x) x, conj_mul w x,
      art_left_of_assoc hassoc htrace hnorm (conj x) (conj w),
      conj_mul (conj x * conj x) (conj w),
      conj_mul (conj x) (conj x),
      conj_conj w, conj_conj x]

/-!
### The chain R → C → H → O, instantiated

ℝ (level 0) is commutative and associative, with trivially central trace and
norm. Each rung consumes exactly what the rungs below produce: C associative;
C commutative (the last commutative rung); H associative; H quadratic. The
payoff: the octonions (CD 3) are alternative.
-/

theorem trace_central_one (x c : CD 1) : (x + conj x) * c = c * (x + conj x) :=
  trace_central_succ trace_central_zero x c

theorem norm_central_one (x c : CD 1) : (x * conj x) * c = c * (x * conj x) :=
  norm_central_succ norm_central_zero x c

theorem trace_central_two (x c : CD 2) : (x + conj x) * c = c * (x + conj x) :=
  trace_central_succ trace_central_one x c

theorem norm_central_two (x c : CD 2) : (x * conj x) * c = c * (x * conj x) :=
  norm_central_succ norm_central_one x c

/-- ℍ is quadratic: associative with central trace and norm. The doubling of
a quadratic algebra is left-alternative -- this is the octonion case. -/
theorem art_left_three (x w : CD 3) : x * (x * w) = (x * x) * w :=
  art_left_of_assoc assoc_two trace_central_two norm_central_two x w

/-- Right-alternativity of the octonions, same hypotheses. -/
theorem art_right_three (w x : CD 3) : (w * x) * x = w * (x * x) :=
  art_right_of_assoc assoc_two trace_central_two norm_central_two w x

/-!
### Chain step (1) of the fold law: ker L_z ≅ ker W

With the code convention z*w = (x*a - b*ȳ, x̄*b + a*y) for z = (x, y),
w = (a, b), the system ker L_z reduces exactly to
(I) b = (x*a)*y and (II) W(a) = (x*a)*y + x*(a*y) = 0, where W is the
ANTI-ASSOCIATOR (claims sheet T12, hand derivation). The derivation uses the
art ONLY through two specific instances -- the left art in x and the right
art in y -- which is what lets the tower consume this theorem level after
level, long after global alternativity is dead.
-/

/-- From a - b = 0, recover a = b. -/
theorem sub_eq_zero {m : ℕ} {a b : CD m} (h : a - b = cdZero) : a = b := by
  have h1 : (a - b) + b = cdZero + b := congrArg (fun t => t + b) h
  rw [sub_add, add_assoc, neg_add_self, add_zero, zero_add] at h1
  exact h1

/-- From A + B = 0, recover B = -A. -/
theorem add_eq_zero_iff_neg {m : ℕ} {A B : CD m} (h : A + B = cdZero) :
    B = neg A := by
  have h1 : neg A + (A + B) = neg A + cdZero := congrArg (fun t => neg A + t) h
  rw [← add_assoc, neg_add_self, zero_add, add_zero] at h1
  exact h1

/-- **Chain step (1).** For imaginary units x, y at level m satisfying the
left art in x and the right art in y, the kernel of left multiplication by
z = (x, y) at level m+1 is an exact copy of the kernel of the
anti-associator W(a) = (x*a)*y + x*(a*y): the pair (a, b) is killed by L_z
iff b is the determined image (x*a)*y and W kills a. -/
theorem ker_Lz_iff_ker_W {m : ℕ} (x y : CD m)
    (hartLx : ∀ w : CD m, x * (x * w) = (x * x) * w)
    (hartRy : ∀ w : CD m, (w * y) * y = w * (y * y))
    (hx : conj x = neg x) (hy : conj y = neg y)
    (hx2 : x * x = neg (cdOne : CD m)) (hy2 : y * y = neg (cdOne : CD m))
    (a b : CD m) :
    dbl x y * dbl a b = (cdZero : CD (m + 1)) ↔
    b = (x * a) * y ∧ (x * a) * y + x * (a * y) = (cdZero : CD m) := by
  constructor
  · intro h
    have h' : dbl (x * a - b * conj y) (conj x * b + a * y)
        = (dbl (cdZero : CD m) (cdZero : CD m) : CD (m + 1)) := h
    injection h' with hidx h1 h2
    -- (I): right-multiply the first component by y (conj y = -y, right art).
    have e1 : (x * a) * y = (b * conj y) * y := by rw [sub_eq_zero h1]
    rw [hy, mul_neg, neg_mul, hartRy b, hy2, mul_neg, mul_one, neg_neg] at e1
    have hI : b = (x * a) * y := e1.symm
    -- (II): left-multiply the second component by x (conj x = -x, left art).
    have h2' : a * y + conj x * b = cdZero := by rw [add_comm, h2]
    have e2 : x * (conj x * b) = x * (neg (a * y)) :=
      by rw [add_eq_zero_iff_neg h2']
    rw [hx, neg_mul, mul_neg, hartLx b, hx2, neg_mul, one_mul, neg_neg, mul_neg] at e2
    have hII : (x * a) * y + x * (a * y) = cdZero := by
      rw [← hI, e2, neg_add_self]
    exact ⟨hI, hII⟩
  · rintro ⟨hI, hII⟩
    -- The image formula turns x*b into the left art in x: x*b = a*y.
    have hB : (x * a) * y = neg (x * (a * y)) :=
      add_eq_zero_iff_neg (by rw [add_comm, hII])
    have hxb : x * b = a * y := by
      rw [hI, hB, mul_neg, hartLx (a * y), hx2, neg_mul, one_mul, neg_neg]
    have c1 : x * a - b * conj y = cdZero := by
      rw [hy, hI, mul_neg, hartRy (x * a), hy2, mul_neg, mul_one, neg_neg,
        sub_self]
    have c2 : conj x * b + a * y = cdZero := by
      rw [hx, neg_mul, hxb, neg_add_self]
    exact congrArg₂ dbl c1 c2

/-!
#### Numeric anchor at the octonion level

The canonical imaginary units of ℂ and ℍ, with all unit facts by
definitional computation, and the iff instantiated at z = i + jℓ ∈ CD 3.
-/

/-- The imaginary unit of ℂ. -/
def imagI : CD 1 := dbl cdZero cdOne

/-- The quaternion unit i, embedded in ℍ. -/
def unitI : CD 2 := dbl imagI cdZero

/-- The new quaternion unit j. -/
def unitJ : CD 2 := dbl cdZero cdOne

theorem conj_imagI : conj imagI = neg imagI := by
  show dbl (conj (cdZero : CD 0)) (neg (cdOne : CD 0))
      = dbl (neg (cdZero : CD 0)) (neg (cdOne : CD 0))
  rw [conj_zero, neg_zero]

theorem imagI_sq : imagI * imagI = neg (cdOne : CD 1) := by
  show dbl ((cdZero : CD 0) * (cdZero : CD 0) - (cdOne : CD 0) * conj (cdOne : CD 0))
      (conj (cdZero : CD 0) * (cdOne : CD 0) + (cdZero : CD 0) * (cdOne : CD 0))
      = dbl (neg (cdOne : CD 0)) (neg (cdZero : CD 0))
  rw [conj_one, mul_one, zero_mul, conj_zero, zero_mul, sub_add, zero_add,
    add_zero, neg_zero]

theorem conj_unitI : conj unitI = neg unitI := by
  show dbl (conj imagI) (neg (cdZero : CD 1))
      = dbl (neg imagI) (neg (cdZero : CD 1))
  rw [conj_imagI]

theorem conj_unitJ : conj unitJ = neg unitJ := by
  show dbl (conj (cdZero : CD 1)) (neg (cdOne : CD 1))
      = dbl (neg (cdZero : CD 1)) (neg (cdOne : CD 1))
  rw [conj_zero, neg_zero]

theorem unitI_sq : unitI * unitI = neg (cdOne : CD 2) := by
  show dbl (imagI * imagI - (cdZero : CD 1) * conj (cdZero : CD 1))
      (conj imagI * (cdZero : CD 1) + imagI * (cdZero : CD 1))
      = dbl (neg (cdOne : CD 1)) (neg (cdZero : CD 1))
  rw [imagI_sq, zero_mul, sub_zero, mul_zero, mul_zero, add_zero, neg_zero]

theorem unitJ_sq : unitJ * unitJ = neg (cdOne : CD 2) := by
  show dbl ((cdZero : CD 1) * (cdZero : CD 1) - (cdOne : CD 1) * conj (cdOne : CD 1))
      (conj (cdZero : CD 1) * (cdOne : CD 1) + (cdZero : CD 1) * (cdOne : CD 1))
      = dbl (neg (cdOne : CD 1)) (neg (cdZero : CD 1))
  rw [conj_one, mul_one, zero_mul, conj_zero, zero_mul, sub_add, zero_add,
    add_zero, neg_zero]

/-- The full alternating art holds at the quaternion level (ℍ is quadratic:
ℂ below it is associative with central trace and norm). -/
theorem art_left_two (x w : CD 2) : x * (x * w) = (x * x) * w :=
  art_left_of_assoc assoc_one trace_central_one norm_central_one x w

theorem art_right_two (w x : CD 2) : (w * x) * x = w * (x * x) :=
  art_right_of_assoc assoc_one trace_central_one norm_central_one w x

/-- Numeric anchor: for z = i + jℓ ∈ CD 3 (octonions), the kernel of L_z is
an exact copy of the kernel of W(a) = (i*a)*j + i*(a*j). -/
theorem ker_Lz_octonion (a b : CD 2) :
    dbl unitI unitJ * dbl a b = (cdZero : CD 3) ↔
    b = (unitI * a) * unitJ ∧ (unitI * a) * unitJ + unitI * (a * unitJ)
      = (cdZero : CD 2) :=
  ker_Lz_iff_ker_W unitI unitJ (art_left_two unitI) (fun w => art_right_two w unitJ)
    conj_unitI conj_unitJ unitI_sq unitJ_sq a b

/-!
#### Chain step (2): diagonal blocks across the doubling

For x, y : CD m and the embedded pair X = (x, 0), Y = (y, 0) : CD (m + 1),
the anti-associator of (X, Y) acting on w = (a₀, a₁) splits into DIAGONAL
blocks: the level-m anti-associator of (x, y) on a₀, and the complementary
block C(u) = y(x̄u) + x̄(yu) = -{L_x, L_y}(u) on a₁ (claims sheet T12,
three-line hand derivation: x·(a₁ℓ₀) = (x̄a₁)ℓ₀ and (a₁ℓ₀)·y = (ya₁)ℓ₀).
Hence ker W at the doubled level is ker W ⊕ ker C, pointwise.
-/

/-- **Chain step (2), block lemma.** The anti-associator
W_T(w) = (X*w)*Y + X*(w*Y) of the embedded pair X = (x,0), Y = (y,0)
decomposes as W_T(a₀, a₁) = (W_A a₀, C a₁): the doubling is DIAGONAL.
No hypotheses -- pure level-m algebra, valid at every floor of the tower,
including the floors where alternativity is dead. -/
theorem W_block {m : ℕ} (x y a₀ a₁ : CD m) :
    (dbl x (cdZero : CD m) * dbl a₀ a₁) * dbl y (cdZero : CD m)
      + dbl x (cdZero : CD m) * (dbl a₀ a₁ * dbl y (cdZero : CD m))
    = dbl ((x * a₀) * y + x * (a₀ * y))
        (y * (conj x * a₁) + conj x * (y * a₁)) := by
  have hXw : dbl x (cdZero : CD m) * dbl a₀ a₁
      = dbl (x * a₀) (conj x * a₁) := by
    show dbl (x * a₀ - a₁ * conj (cdZero : CD m))
        (conj x * a₁ + a₀ * (cdZero : CD m)) = dbl (x * a₀) (conj x * a₁)
    rw [conj_zero, mul_zero, sub_zero, mul_zero, add_zero]
  have hwY : dbl a₀ a₁ * dbl y (cdZero : CD m)
      = dbl (a₀ * y) (y * a₁) := by
    show dbl (a₀ * y - (cdZero : CD m) * conj a₁)
        (conj a₀ * (cdZero : CD m) + y * a₁) = dbl (a₀ * y) (y * a₁)
    rw [zero_mul, mul_zero, sub_zero, zero_add]
  have h1 : (dbl x (cdZero : CD m) * dbl a₀ a₁) * dbl y (cdZero : CD m)
      = dbl ((x * a₀) * y) (y * (conj x * a₁)) := by
    rw [hXw]
    show dbl ((x * a₀) * y - (cdZero : CD m) * conj (conj x * a₁))
        (conj (x * a₀) * (cdZero : CD m) + y * (conj x * a₁))
        = dbl ((x * a₀) * y) (y * (conj x * a₁))
    rw [zero_mul, mul_zero, sub_zero, zero_add]
  have h2 : dbl x (cdZero : CD m) * (dbl a₀ a₁ * dbl y (cdZero : CD m))
      = dbl (x * (a₀ * y)) (conj x * (y * a₁)) := by
    rw [hwY]
    show dbl (x * (a₀ * y) - (y * a₁) * conj (cdZero : CD m))
        (conj x * (y * a₁) + (a₀ * y) * (cdZero : CD m))
        = dbl (x * (a₀ * y)) (conj x * (y * a₁))
    rw [conj_zero, mul_zero, sub_zero, mul_zero, add_zero]
  rw [h1, h2]
  rfl

/-- **Chain step (2), kernel split.** The kernel of the doubled
anti-associator is the direct product of the two diagonal blocks:
(a₀, a₁) is killed iff W kills a₀ AND C kills a₁. This is the claims
sheet's ker W_T = ker W_A ⊕ ker C, pointwise. -/
theorem ker_WT_iff {m : ℕ} (x y a₀ a₁ : CD m) :
    (dbl x (cdZero : CD m) * dbl a₀ a₁) * dbl y (cdZero : CD m)
      + dbl x (cdZero : CD m) * (dbl a₀ a₁ * dbl y (cdZero : CD m))
      = (cdZero : CD (m + 1)) ↔
    (x * a₀) * y + x * (a₀ * y) = (cdZero : CD m) ∧
    y * (conj x * a₁) + conj x * (y * a₁) = (cdZero : CD m) := by
  rw [W_block]
  constructor
  · intro h
    have h' : dbl ((x * a₀) * y + x * (a₀ * y))
          (y * (conj x * a₁) + conj x * (y * a₁))
        = (dbl (cdZero : CD m) (cdZero : CD m) : CD (m + 1)) := h
    injection h' with hidx h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact congrArg₂ dbl h1 h2

/-- For imaginary x (conj x = -x), the complementary block C is the NEGATIVE
anti-commutator of the left multiplications: C(u) = -{L_x, L_y}(u), the
claims sheet's C = -{L_x, L_y}. -/
theorem C_eq_neg_anticommutator {m : ℕ} (x y u : CD m) (hx : conj x = neg x) :
    y * (conj x * u) + conj x * (y * u)
      = neg (y * (x * u) + x * (y * u)) := by
  rw [hx, neg_mul, neg_mul, mul_neg, neg_add]

/-- Negation is componentwise on doubles (definitional). -/
theorem neg_dbl {m : ℕ} (a b : CD m) : neg (dbl a b) = dbl (neg a) (neg b) := rfl

/-!
#### Chain step (3): H(x, y) ⊂ ker C

The quaternion H = span{1, x, y, xy} sits inside the kernel of the
complementary block C(u) = y(x̄u) + x̄(yu) for every Fano pair of imaginary
units: C kills 1, x, y and xy. The derivation consumes only the two art
instances of step (1) plus the two anti-commutation facts of the pair
(hxy : yx = -(xy), hyxy : y(xy) = -((xy)y)) -- the polarisation of the
alternating associator (claims sheet T6/T12). All hypotheses are closed
by definitional computation at the octonionic anchor below.
-/

section Step3

/-- **C(1) = 0**: the anti-commutator polarisation kills the identity. -/
theorem C_ker_one {m : ℕ} (x y : CD m) (hx : conj x = neg x)
    (hxy : y * x = neg (x * y)) :
    y * (conj x * (cdOne : CD m)) + conj x * (y * (cdOne : CD m))
      = (cdZero : CD m) := by
  rw [hx, neg_mul, mul_neg, mul_one, mul_one, neg_mul, hxy, neg_neg,
    add_neg_self]

/-- **C(x) = 0**: x̄x = 1 and the left art x(xy) = (x²)y = -y. -/
theorem C_ker_x {m : ℕ} (x y : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m)) (hxy : y * x = neg (x * y))
    (hartLx : ∀ w : CD m, x * (x * w) = (x * x) * w) :
    y * (conj x * x) + conj x * (y * x) = (cdZero : CD m) := by
  have e1 : conj x * x = (cdOne : CD m) := by
    rw [hx, neg_mul, hx2, neg_neg]
  have e2 : x * (x * y) = neg y := by
    rw [hartLx y, hx2, neg_mul, one_mul]
  rw [e1, mul_one, hxy, mul_neg, hx, neg_mul, neg_neg, e2, add_neg_self]

/-- **C(y) = 0**: y(xy) = -((xy)y) = -x(y²) = x by the right art. -/
theorem C_ker_y {m : ℕ} (x y : CD m) (hx : conj x = neg x)
    (hy2 : y * y = neg (cdOne : CD m))
    (hyxy : y * (x * y) = neg ((x * y) * y))
    (hartRy : ∀ w : CD m, (w * y) * y = w * (y * y)) :
    y * (conj x * y) + conj x * (y * y) = (cdZero : CD m) := by
  have e1 : x * (y * y) = neg x := by rw [hy2, mul_neg, mul_one]
  have e2 : y * (x * y) = x := by rw [hyxy, hartRy x, e1, neg_neg]
  rw [hy2, mul_neg, mul_one, hx, neg_mul, mul_neg, e2, neg_neg, neg_add_self]

/-- **C(xy) = 0**: the whole quaternion H = span{1, x, y, xy} dies in C. -/
theorem C_ker_xy {m : ℕ} (x y : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m)) (hy2 : y * y = neg (cdOne : CD m))
    (hyxy : y * (x * y) = neg ((x * y) * y))
    (hartLx : ∀ w : CD m, x * (x * w) = (x * x) * w)
    (hartRy : ∀ w : CD m, (w * y) * y = w * (y * y)) :
    y * (conj x * (x * y)) + conj x * (y * (x * y)) = (cdZero : CD m) := by
  have eL : x * (x * y) = neg y := by rw [hartLx y, hx2, neg_mul, one_mul]
  have eR : y * (x * y) = x := by
    rw [hyxy, hartRy x, hy2, mul_neg, mul_one, neg_neg]
  rw [hx, neg_mul, mul_neg, eL, mul_neg, hy2, neg_neg, eR, neg_mul, hx2,
    neg_neg, neg_add_self]

end Step3

/-!
#### Octonionic anchor of step (3)

The two anti-commutation hypotheses hold by definitional computation for
the concrete quaternion units i = (imagI, 0), j = (0, 1): ij = (0, -i),
ji = (0, i), j(ij) = i = -((ij)j). Hence the whole quaternion
H = span{1, i, j, ij} ⊂ ker C at the ℍ level that doubles into 𝕆.
-/

theorem unitI_mul_unitJ : unitI * unitJ = dbl (cdZero : CD 1) (neg imagI) := by
  show dbl (imagI * (cdZero : CD 1) - (cdOne : CD 1) * conj (cdZero : CD 1))
      (conj imagI * (cdOne : CD 1) + (cdZero : CD 1) * (cdZero : CD 1))
      = dbl (cdZero : CD 1) (neg imagI)
  rw [mul_zero, conj_zero, mul_zero, sub_zero, conj_imagI, neg_mul, mul_one,
    zero_mul, add_zero]

theorem unitJ_mul_unitI : unitJ * unitI = dbl (cdZero : CD 1) imagI := by
  show dbl ((cdZero : CD 1) * imagI - (cdZero : CD 1) * conj (cdOne : CD 1))
      (conj (cdZero : CD 1) * (cdZero : CD 1) + imagI * (cdOne : CD 1))
      = dbl (cdZero : CD 1) imagI
  rw [zero_mul, conj_one, zero_mul, sub_self, conj_zero, zero_mul, mul_one,
    zero_add]

theorem hxy_units : unitJ * unitI = neg (unitI * unitJ) := by
  rw [unitJ_mul_unitI, unitI_mul_unitJ, neg_dbl, neg_neg, neg_zero]

theorem hyxy_units :
    unitJ * (unitI * unitJ) = neg ((unitI * unitJ) * unitJ) := by
  have h1 : unitJ * (unitI * unitJ) = dbl imagI (cdZero : CD 1) := by
    rw [unitI_mul_unitJ]
    show dbl ((cdZero : CD 1) * (cdZero : CD 1) - neg imagI * conj (cdOne : CD 1))
        (conj (cdZero : CD 1) * neg imagI + (cdZero : CD 1) * (cdOne : CD 1))
        = dbl imagI (cdZero : CD 1)
    rw [zero_mul, conj_one, neg_mul, mul_one, sub_add, neg_neg, zero_add,
      conj_zero, zero_mul, zero_mul, zero_add]
  have h2 : (unitI * unitJ) * unitJ = dbl (neg imagI) (cdZero : CD 1) := by
    rw [unitI_mul_unitJ]
    show dbl ((cdZero : CD 1) * (cdZero : CD 1) - (cdOne : CD 1) * conj (neg imagI))
        (conj (cdZero : CD 1) * (cdOne : CD 1) + (cdZero : CD 1) * neg imagI)
        = dbl (neg imagI) (cdZero : CD 1)
    rw [conj_neg, conj_imagI, neg_neg, one_mul, zero_mul, sub_add, zero_add,
      conj_zero, zero_mul, mul_neg, zero_mul, neg_zero, zero_add]
  rw [h1, h2, neg_dbl, neg_neg, neg_zero]

/-- **Numeric anchor of step (3).** For the concrete quaternion pair
(i, j) whose double is the octonion z = i + jℓ, the complementary block
C(u) = j(īu) + ī(ju) kills the entire quaternion H = span{1, i, j, ij}. -/
theorem C_ker_H_octonion :
    unitJ * (conj unitI * (cdOne : CD 2)) + conj unitI * (unitJ * (cdOne : CD 2))
      = (cdZero : CD 2)
    ∧ unitJ * (conj unitI * unitI) + conj unitI * (unitJ * unitI)
      = (cdZero : CD 2)
    ∧ unitJ * (conj unitI * unitJ) + conj unitI * (unitJ * unitJ)
      = (cdZero : CD 2)
    ∧ unitJ * (conj unitI * (unitI * unitJ))
        + conj unitI * (unitJ * (unitI * unitJ)) = (cdZero : CD 2) :=
  ⟨C_ker_one unitI unitJ conj_unitI hxy_units,
   C_ker_x unitI unitJ conj_unitI unitI_sq hxy_units (art_left_two unitI),
   C_ker_y unitI unitJ conj_unitI unitJ_sq hyxy_units
     (fun w => art_right_two w unitJ),
   C_ker_xy unitI unitJ conj_unitI unitI_sq unitJ_sq hyxy_units
     (art_left_two unitI) (fun w => art_right_two w unitJ)⟩

/-!
### Step (4) of the T12 chain: x·ker W ⊆ ker C

Polarising the left art u·(u·w) = (u·u)·w in u and instantiating at
the anticommuting pair (x, y) gives x·(y·(x·a)) = y·a for EVERY a, so
C(x·a) = y·a − x·(y·(x·a)) = 0 identically: C∘L_x = 0. Step (4)
(x·ker W ⊆ ker C) follows a fortiori — the hypothesis W(a) = 0 is
never used. This matches the census: at the ℍ rung L_x is invertible,
so C vanishes on all of ℍ and dim ker C = 4 + dim ker W there.
-/

/-- Cancellation on the left. -/
theorem add_left_cancel {m : ℕ} (p q r : CD m) (h : p + q = p + r) : q = r := by
  have h2 : neg p + (p + q) = neg p + (p + r) := by rw [h]
  rw [← add_assoc, neg_add_self, zero_add, ← add_assoc, neg_add_self, zero_add] at h2
  exact h2

/-- Cancellation on the right. -/
theorem add_right_cancel {m : ℕ} (p q r : CD m) (h : q + p = r + p) : q = r := by
  have h2 : (q + p) + neg p = (r + p) + neg p := by rw [h]
  rw [add_assoc, add_assoc, add_neg_self, add_zero, add_zero] at h2
  exact h2

/-- Polarised left art: linearise u·(u·w) = (u·u)·w in u. -/
theorem art_left_lin {m : ℕ} (hLart : ∀ u w : CD m, u * (u * w) = (u * u) * w)
    (u v w : CD m) :
    u * (v * w) + v * (u * w) = (u * v) * w + (v * u) * w := by
  have hL : (u + v) * ((u + v) * w)
      = (u * (u * w) + u * (v * w)) + (v * (u * w) + v * (v * w)) := by
    rw [add_mul', add_mul', mul_add', mul_add']
  have hR : ((u + v) * (u + v)) * w
      = ((u * u) * w + (u * v) * w) + ((v * u) * w + (v * v) * w) := by
    rw [add_mul', mul_add', mul_add', add_mul', add_mul', add_mul']
  have key := hL.symm.trans ((hLart (u + v) w).trans hR)
  rw [hLart u w, hLart v w, add_assoc, add_assoc] at key
  have h1 := add_left_cancel _ _ _ key
  rw [← add_assoc, ← add_assoc] at h1
  exact add_right_cancel _ _ _ h1

/-- **Step (4), pointwise form: C∘L_x = 0.** For anticommuting imaginary
x, y at a left-alternative level, C(x·a) = 0 for EVERY a. -/
theorem C_comp_Lx_eq_zero {m : ℕ} (x y a : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m)) (hxy : y * x = neg (x * y))
    (hLart : ∀ u w : CD m, u * (u * w) = (u * u) * w) :
    y * (conj x * (x * a)) + conj x * (y * (x * a)) = (cdZero : CD m) := by
  have hxa : x * (x * a) = neg a := by
    rw [hLart x a, hx2, neg_mul, one_mul]
  have key : x * (y * (x * a)) + y * (x * (x * a)) = (cdZero : CD m) := by
    have e := art_left_lin hLart x y (x * a)
    rw [hxy, neg_mul, add_neg_self] at e
    exact e
  have hkey : x * (y * (x * a)) = y * a := by
    rw [hxa, mul_neg] at key
    have h2 : x * (y * (x * a)) - y * a = (cdZero : CD m) := by
      rw [sub_add]
      exact key
    exact sub_eq_zero h2
  rw [hx, neg_mul, neg_mul, mul_neg, hxa, mul_neg, neg_neg, hkey, add_neg_self]

/-- **Step (4) as stated in the chain:** x·ker W ⊆ ker C, pointwise.
`W(a) = 0` is recorded for the chain link but not needed — the theorem
above is strictly stronger. -/
theorem x_mul_ker_W_subset_ker_C {m : ℕ} (x y a : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m)) (hxy : y * x = neg (x * y))
    (hLart : ∀ u w : CD m, u * (u * w) = (u * u) * w)
    (_hW : (x * a) * y + x * (a * y) = (cdZero : CD m)) :
    y * (conj x * (x * a)) + conj x * (y * (x * a)) = (cdZero : CD m) :=
  C_comp_Lx_eq_zero x y a hx hx2 hxy hLart

/-- **Numeric anchor of step (4).** For the quaternion pair (i, j) whose
double is z = i + jℓ ∈ 𝕆: C(i·a) = 0 for every quaternion a. -/
theorem C_comp_Lx_octonion (a : CD 2) :
    unitJ * (conj unitI * (unitI * a)) + conj unitI * (unitJ * (unitI * a))
      = (cdZero : CD 2) :=
  C_comp_Lx_eq_zero unitI unitJ a conj_unitI unitI_sq hxy_units art_left_two

/-!
### Step (5) of the T12 chain: H ∩ x·ker W = 0

The claims sheet's three-line directness proof: if h = x·a ∈ H then
a = x̄h by left art and injectivity; x̄·H = H; and W|_H is invertible,
so W(a) = W(x̄h) = 0 forces h = 0. The general-level statement needs
H = span{1, x, y, xy} as a coefficient space plus linear independence
(the linear-algebra layer that steps (6)-(7) also need), so here we
deliver the two algebraic engines and the full numeric anchor. At the
ℍ rung H(i, j) = ℍ is ALL of ℍ, so the directness reduces to
ker W(i, j) = 0 -- and that closes by associativity of ℍ plus two-sided
cancellation.
-/

/-- Characteristic zero, componentwise: a + a = 0 forces a = 0. -/
theorem add_self_eq_zero {m : ℕ} (a : CD m) (h : a + a = cdZero) : a = cdZero := by
  induction m with
  | zero =>
    cases a with
    | zero r =>
      have h' : zero (r + r) = zero 0 := h
      injection h' with h1
      exact congrArg zero (by linarith)
  | succ n ih =>
    cases a with
    | dbl x y =>
      have h' : dbl (x + x) (y + y)
          = (dbl (cdZero : CD n) (cdZero : CD n) : CD (n + 1)) := h
      injection h' with hidx h1 h2
      exact congrArg₂ dbl (ih x h1) (ih y h2)

/-- **L_x is injective (by the left art).** At any left-alternative
level, an imaginary unit x has x·a = 0 only for a = 0: apply x̄ = -x
to the left and use x·(x·a) = (x·x)·a = -a. This is the injectivity
half of step (6). -/
theorem Lx_inj {m : ℕ} (x a : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m))
    (hLart : ∀ u w : CD m, u * (u * w) = (u * u) * w)
    (h : x * a = (cdZero : CD m)) : a = (cdZero : CD m) := by
  have h2 : conj x * (x * a) = conj x * (cdZero : CD m) := by rw [h]
  rw [hx, neg_mul, hLart x a, hx2, neg_mul, one_mul, neg_neg, mul_zero] at h2
  exact h2

/-- **Numeric anchor of step (5): W|_H is injective.** At the ℍ rung the
quaternion H(x, y) is all of ℍ, so the directness H ∩ x·ker W = 0
reduces to ker W(i, j) = 0. -/
theorem W_inj_quaternion (a : CD 2)
    (hW : (unitI * a) * unitJ + unitI * (a * unitJ) = (cdZero : CD 2)) :
    a = (cdZero : CD 2) := by
  rw [assoc_two] at hW
  have h1 : unitI * (a * unitJ) = (cdZero : CD 2) := add_self_eq_zero _ hW
  have h2 : a * unitJ = (cdZero : CD 2) :=
    Lx_inj unitI (a * unitJ) conj_unitI unitI_sq art_left_two h1
  have h3 : (a * unitJ) * conj unitJ = (cdZero : CD 2) * conj unitJ := by rw [h2]
  rw [assoc_two, conj_unitJ, mul_neg, unitJ_sq, neg_neg, mul_one, zero_mul] at h3
  exact h3

/-- **Step (5) at the octonionic anchor: H ∩ x·ker W = 0.** If
W(a) = 0 at the ℍ rung, the H-component x·a of the fold vanishes. -/
theorem x_mul_kerW_inter_H_octonion (a : CD 2)
    (hW : (unitI * a) * unitJ + unitI * (a * unitJ) = (cdZero : CD 2)) :
    unitI * a = (cdZero : CD 2) := by
  rw [W_inj_quaternion a hW, mul_zero]

/-!
### The fold law, kernel form (art levels): steps (6)-(7) collapsed

At a left-alternative level the whole chain telescopes. First, L_x is
SURJECTIVE constructively: x·(x̄·u) = u for every u (left art applied to
x̄, with x̄x̄ = x² = -1). Hence C ≡ 0 identically (step (4) says C∘L_x
is already zero), so in the block decomposition ker W_T = ker W_A ⊕
ker C the second block is EVERYTHING: the kernel of the anti-associator
DOUBLES as ker W ⊕ (free ℓ-block). With the base ker W(i, j)|ℍ = 0
(step 5), induction gives ker W_m = {a₀ ∈ ker W_{m-1}} and dimension
2^m - 4 at every art rung: the 16-census value 4 and the 32-census
value 12 for old pairs, machine-checked. Beyond art levels (m ≥ 4,
sedenions) C ≡ 0 is numeric-only (check F, 930/930) -- the identity
needs the alternativity that dies there. The dimension bookkeeping as
`finrank` arithmetic is the remaining linear-algebra layer.
-/

/-- **L_x is surjective (constructive).** Every u is x·(x̄u): left art on
x̄ with x̄·x̄ = x·x = -1. -/
theorem Lx_surj {m : ℕ} (x u : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m))
    (hLart : ∀ u w : CD m, u * (u * w) = (u * u) * w) :
    x * (conj x * u) = u := by
  rw [hx, neg_mul, mul_neg, hLart x u, hx2, neg_mul, one_mul, neg_neg]

/-- **At art levels the complementary block vanishes identically.**
C(u) = 0 for every u: u lies in the image of L_x, and C∘L_x = 0. This
collapses the claims sheet's step (6): dim ker C = dim A = 2^m, which
is 4 + dim ker W exactly when dim ker W = 2^m - 4 (the induction). -/
theorem C_eq_zero {m : ℕ} (x y : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m)) (hxy : y * x = neg (x * y))
    (hLart : ∀ u w : CD m, u * (u * w) = (u * u) * w) (u : CD m) :
    y * (conj x * u) + conj x * (y * u) = (cdZero : CD m) := by
  have hu : u = x * (conj x * u) := (Lx_surj x u hx hx2 hLart).symm
  rw [hu]
  exact C_comp_Lx_eq_zero x y (conj x * u) hx hx2 hxy hLart

/-- **THE FOLD LAW, kernel form.** For anticommuting imaginary x, y at
a left-alternative level, the kernel of the doubled anti-associator is
ker W ⊕ (free ℓ-block): W_T kills (a₀, a₁) iff W_A kills a₀ alone. -/
theorem ker_W_fold {m : ℕ} (x y a₀ a₁ : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m)) (hxy : y * x = neg (x * y))
    (hLart : ∀ u w : CD m, u * (u * w) = (u * u) * w) :
    (dbl x (cdZero : CD m) * dbl a₀ a₁) * dbl y (cdZero : CD m)
      + dbl x (cdZero : CD m) * (dbl a₀ a₁ * dbl y (cdZero : CD m))
      = (cdZero : CD (m + 1)) ↔
    (x * a₀) * y + x * (a₀ * y) = (cdZero : CD m) := by
  rw [ker_WT_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, C_eq_zero x y hx hx2 hxy hLart a₁⟩⟩

/-- **Numeric anchor of the fold law: the 16-census value 4.** For the
pair (i, j) whose ℓ-double is z = i + jℓ ∈ CD 3, the doubled kernel is
ker W|ℍ ⊕ ℍ = {0} ⊕ ℍ (dimension 4, the 16-census nullity of (1, 2));
one rung higher, the same theorem with art at CD 3 gives the 32-census
value 12 for old pairs. -/
theorem ker_W_octonion_fold (a₀ a₁ : CD 2) :
    (dbl unitI (cdZero : CD 2) * dbl a₀ a₁) * dbl unitJ (cdZero : CD 2)
      + dbl unitI (cdZero : CD 2) * (dbl a₀ a₁ * dbl unitJ (cdZero : CD 2))
      = (cdZero : CD 3) ↔
    a₀ = (cdZero : CD 2) := by
  rw [ker_W_fold unitI unitJ a₀ a₁ conj_unitI unitI_sq hxy_units art_left_two]
  constructor
  · intro h
    exact W_inj_quaternion a₀ h
  · intro h
    rw [h, mul_zero, zero_mul, mul_zero, add_zero]

/-!
### The finrank layer, phase A: module structure

To state "dim ker W" as a number we need CD m to be a genuine ℝ-module.
Scalar action r•a is componentwise recursion; the tower addition and
negation already satisfy the abelian-group laws (proved above), so the
only new content is the scalar bookkeeping and its compatibility with
the Cayley-Dickson multiplication: r•(a*b) = (r•a)*b = a*(r•b), which
is what makes W_A and W_T linear.
-/

/-- Scalar multiplication: componentwise recursion down the tower. -/
def cdSmul : ∀ {m : ℕ}, ℝ → CD m → CD m
  | 0, r, zero s => zero (r * s)
  | _ + 1, r, dbl x y => dbl (cdSmul r x) (cdSmul r y)

theorem smul_zero {m : ℕ} (r : ℝ) : cdSmul r (cdZero : CD m) = cdZero := by
  induction m with
  | zero => exact congrArg zero (show r * (0:ℝ) = 0 by ring)
  | succ n ih => exact congrArg₂ dbl ih ih

theorem zero_smul' {m : ℕ} (a : CD m) : cdSmul 0 a = cdZero := by
  induction m with
  | zero =>
    cases a with
    | zero s => exact congrArg zero (show (0:ℝ) * s = 0 by ring)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem one_smul' {m : ℕ} (a : CD m) : cdSmul 1 a = a := by
  induction m with
  | zero =>
    cases a with
    | zero s => exact congrArg zero (_root_.one_mul s)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem smul_neg {m : ℕ} (r : ℝ) (a : CD m) : cdSmul r (neg a) = neg (cdSmul r a) := by
  induction m with
  | zero =>
    cases a with
    | zero s => exact congrArg zero (_root_.mul_neg r s)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem smul_add' {m : ℕ} (r : ℝ) (a b : CD m) :
    cdSmul r (a + b) = cdSmul r a + cdSmul r b := by
  induction m with
  | zero =>
    cases a with
    | zero s =>
      cases b with
      | zero t => exact congrArg zero (_root_.mul_add r s t)
  | succ n ih =>
    cases a with
    | dbl x y =>
      cases b with
      | dbl u v => exact congrArg₂ dbl (ih x u) (ih y v)

theorem add_smul' {m : ℕ} (r s : ℝ) (a : CD m) :
    cdSmul (r + s) a = cdSmul r a + cdSmul s a := by
  induction m with
  | zero =>
    cases a with
    | zero t => exact congrArg zero (_root_.add_mul r s t)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem mul_smul' {m : ℕ} (r s : ℝ) (a : CD m) :
    cdSmul (r * s) a = cdSmul r (cdSmul s a) := by
  induction m with
  | zero =>
    cases a with
    | zero t => exact congrArg zero (_root_.mul_assoc r s t)
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (ih y)

theorem smul_sub {m : ℕ} (r : ℝ) (a b : CD m) :
    cdSmul r (a - b) = cdSmul r a - cdSmul r b := by
  rw [sub_add, smul_add', smul_neg, ← sub_add]

theorem smul_conj {m : ℕ} (r : ℝ) (a : CD m) :
    conj (cdSmul r a) = cdSmul r (conj a) := by
  induction m with
  | zero =>
    cases a with
    | zero s => rfl
  | succ n ih =>
    cases a with
    | dbl x y => exact congrArg₂ dbl (ih x) (smul_neg r y).symm

/-- The scalar passes through the Cayley-Dickson multiplication on
either side: (r•a)*b = r•(a*b) = a*(r•b). This is the linearity
engine for W_A and W_T. -/
theorem smul_mul_smul {m : ℕ} (r : ℝ) (a b : CD m) :
    cdSmul r a * b = cdSmul r (a * b) ∧ a * cdSmul r b = cdSmul r (a * b) := by
  induction m with
  | zero =>
    cases a with
    | zero s =>
      cases b with
      | zero t =>
        constructor
        · exact congrArg zero (mul_assoc r s t)
        · exact congrArg zero (mul_left_comm s r t)
  | succ n ih =>
    have h1 : ∀ a b : CD n, cdSmul r a * b = cdSmul r (a * b) := fun a b => (ih a b).1
    have h2 : ∀ a b : CD n, a * cdSmul r b = cdSmul r (a * b) := fun a b => (ih a b).2
    cases a with
    | dbl p q =>
      cases b with
      | dbl u v =>
        have c1 : cdSmul r p * u - v * conj (cdSmul r q)
            = cdSmul r (p * u - v * conj q) := by
          rw [h1 p u, smul_conj, h2 v (conj q), smul_sub]
        have c2 : conj (cdSmul r p) * v + u * cdSmul r q
            = cdSmul r (conj p * v + u * q) := by
          rw [smul_conj, h1 (conj p) v, h2 u q, smul_add']
        have c3 : p * cdSmul r u - cdSmul r v * conj q
            = cdSmul r (p * u - v * conj q) := by
          rw [h2 p u, h1 v (conj q), smul_sub]
        have c4 : conj p * cdSmul r v + cdSmul r u * q
            = cdSmul r (conj p * v + u * q) := by
          rw [h2 (conj p) v, h1 u q, smul_add']
        constructor
        · exact congrArg₂ dbl c1 c2
        · exact congrArg₂ dbl c3 c4

theorem smul_mul_left {m : ℕ} (r : ℝ) (a b : CD m) :
    cdSmul r a * b = cdSmul r (a * b) := (smul_mul_smul r a b).1

theorem smul_mul_right {m : ℕ} (r : ℝ) (a b : CD m) :
    a * cdSmul r b = cdSmul r (a * b) := (smul_mul_smul r a b).2

/-!
### The finrank layer, phase B: abelian group + module instances

The tower was an abelian group all along; the instances below just
register the structure Mathlib needs. All fields are the ad-hoc lemmas
proved earlier in the file, so no new mathematics -- only bookkeeping.
The `Add`/`Neg`/`Sub` instances at the top of the file remain in
scope and are definitionally equal to the projections below.
-/

instance cdZeroInst {m : ℕ} : Zero (CD m) := ⟨cdZero⟩

instance cdAddCommGroup {m : ℕ} : AddCommGroup (CD m) where
  add := add
  add_assoc := add_assoc
  zero := cdZero
  zero_add := zero_add
  add_zero := add_zero
  neg := neg
  sub := sub
  sub_eq_add_neg := sub_add
  neg_add_cancel := neg_add_self
  add_comm := add_comm
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul := zsmulRec
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

instance cdModule {m : ℕ} : Module ℝ (CD m) where
  smul := cdSmul
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_zero := smul_zero
  smul_add := smul_add'
  zero_smul := zero_smul'
  add_smul := add_smul'

/-!
### The finrank layer, phase B: the tower as linear maps and its dimension

Left/right multiplication are linear (the scalar-passes-through lemmas
of phase A are exactly their `map_smul'`), so W_A and W_T assemble from
them with zero proof burden. The doubling dbl is a linear bijection
CD m × CD m ≃ CD (m+1), so finrank (CD m) = 2^m by induction. With
Module.Finite registered, rank-nullity applies.
-/

/-- Left multiplication as a genuine linear map. -/
def mulLeft {m : ℕ} (x : CD m) : CD m →ₗ[ℝ] CD m where
  toFun a := x * a
  map_add' a b := mul_add' x a b
  map_smul' r a := smul_mul_right r x a

/-- Right multiplication as a genuine linear map. -/
def mulRight {m : ℕ} (y : CD m) : CD m →ₗ[ℝ] CD m where
  toFun a := a * y
  map_add' a b := add_mul' y a b
  map_smul' r a := smul_mul_left r a y

/-- The diagonal anti-associator W_A a = (x·a)·y + x·(a·y), linear in a. -/
def WA {m : ℕ} (x y : CD m) : CD m →ₗ[ℝ] CD m :=
  (mulRight y).comp (mulLeft x) + (mulLeft x).comp (mulRight y)

/-- The doubled anti-associator W_T on CD (m+1), with x, y embedded
as real pairs. -/
def WT {m : ℕ} (x y : CD m) : CD (m + 1) →ₗ[ℝ] CD (m + 1) :=
  (mulRight (dbl y (cdZero : CD m))).comp (mulLeft (dbl x (cdZero : CD m)))
    + (mulLeft (dbl x (cdZero : CD m))).comp (mulRight (dbl y (cdZero : CD m)))

/-- The doubling as a linear map. -/
def cdPairLm {m : ℕ} : CD m × CD m →ₗ[ℝ] CD (m + 1) where
  toFun p := dbl p.1 p.2
  map_add' p q := rfl
  map_smul' r p := rfl

theorem cdPairLm_injective {m : ℕ} : Function.Injective (cdPairLm (m := m)) := by
  intro a b h
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  have h' : dbl a₁ a₂ = dbl b₁ b₂ := h
  injection h' with hidx h1 h2
  exact Prod.ext h1 h2

theorem cdPairLm_surjective {m : ℕ} : Function.Surjective (cdPairLm (m := m)) := by
  intro v
  cases v with
  | dbl a b => exact ⟨(a, b), rfl⟩

/-- The pair-of-levels form: W_T read through the doubling bijection. -/
def WTP {m : ℕ} (x y : CD m) : CD m × CD m →ₗ[ℝ] CD (m + 1) :=
  (WT x y).comp cdPairLm

/-- Embedding the level-m anti-associator into level m+1 reproduces
the doubled anti-associator of level m, definitionally. -/
theorem WA_eq_WT_embed {m : ℕ} (x y : CD m) :
    WA (dbl x (cdZero : CD m)) (dbl y (cdZero : CD m)) = WT x y := rfl

/-- The inverse of the doubling, as a linear map. -/
def cdUnpair {m : ℕ} : CD (m + 1) → CD m × CD m
  | dbl a b => (a, b)

def cdUnpairLm {m : ℕ} : CD (m + 1) →ₗ[ℝ] CD m × CD m where
  toFun := cdUnpair
  map_add' v w := by
    cases v with
    | dbl x y =>
      cases w with
      | dbl u z => rfl
  map_smul' r v := by
    cases v with
    | dbl x y => rfl

theorem cdUnpair_injective {m : ℕ} : Function.Injective (cdUnpair (m := m)) := by
  intro a b h
  cases a with
  | dbl x y =>
    cases b with
    | dbl u z =>
      have hp : (x, y) = (u, z) := h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hp
      exact congrArg₂ dbl h1 h2

theorem cdUnpair_surjective {m : ℕ} : Function.Surjective (cdUnpair (m := m)) := by
  intro p
  obtain ⟨a, b⟩ := p
  exact ⟨dbl a b, rfl⟩

/-- The doubling bijection as a linear equivalence. -/
noncomputable def cdSuccEquiv {m : ℕ} : CD (m + 1) ≃ₗ[ℝ] CD m × CD m :=
  LinearEquiv.ofBijective cdUnpairLm ⟨cdUnpair_injective, cdUnpair_surjective⟩

/-- Level zero is the ground field. -/
def cdZeroRe (a : CD 0) : ℝ := match a with | zero r => r

def cdZeroMap : CD 0 →ₗ[ℝ] ℝ where
  toFun := cdZeroRe
  map_add' a b := by
    cases a with
    | zero r =>
      cases b with
      | zero s => rfl
  map_smul' r a := by
    cases a with
    | zero s => rfl

theorem cdZeroMap_injective : Function.Injective (cdZeroMap : CD 0 → ℝ) := by
  intro a b h
  cases a with
  | zero r =>
    cases b with
    | zero s =>
      have h' : r = s := h
      exact congrArg zero h'

theorem cdZeroMap_surjective : Function.Surjective (cdZeroMap : CD 0 → ℝ) := by
  intro r
  exact ⟨zero r, rfl⟩

noncomputable def cdZeroEquiv : CD 0 ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective cdZeroMap ⟨cdZeroMap_injective, cdZeroMap_surjective⟩

instance cdFinite {m : ℕ} : Module.Finite ℝ (CD m) := by
  induction m with
  | zero => exact Module.Finite.equiv cdZeroEquiv.symm
  | succ n ih =>
      haveI := ih
      exact Module.Finite.equiv (cdSuccEquiv (m := n)).symm

/-- **Dimension of the tower.** finrank (CD m) = 2^m: every doubling
doubles the dimension, and CD 0 is ℝ. -/
theorem finrank_cd (m : ℕ) : Module.finrank ℝ (CD m) = 2 ^ m := by
  induction m with
  | zero =>
    rw [LinearEquiv.finrank_eq cdZeroEquiv, Module.finrank_self, pow_zero]
  | succ n ih =>
    rw [LinearEquiv.finrank_eq cdSuccEquiv, Module.finrank_prod, ih,
      pow_succ, Nat.mul_two]

/-!
### The finrank layer, phase C: the fold law as an equation between numbers

Rank-nullity turns the kernel decomposition of `ker_W_fold` into the
numeric fold law: dim ker W_{m+1} = dim ker W_m + 2^m at every
left-alternative rung. With the base dim ker W(i, j)|ℍ = 0 (step 5)
this yields the census values machine-checked: 4 at the octonions
(16-census, pair (1,2)) and 12 at the sedenions (32-census).
-/

/-- Kernel decomposition through the pairing: W_T kills (a₀, a₁) iff
W_A kills a₀ -- the `ker_W_fold` Iff, read as a submodule identity. -/
theorem ker_WTP_eq {m : ℕ} (x y : CD m)
    (hx : conj x = neg x) (hx2 : x * x = neg (cdOne : CD m))
    (hxy : y * x = neg (x * y))
    (hLart : ∀ u w : CD m, u * (u * w) = (u * u) * w) :
    LinearMap.ker (WTP x y)
      = LinearMap.ker ((WA x y).comp (LinearMap.fst ℝ (CD m) (CD m))) := by
  ext p
  constructor
  · intro h
    exact LinearMap.mem_ker.mpr
      ((ker_W_fold x y p.1 p.2 hx hx2 hxy hLart).mp (LinearMap.mem_ker.mp h))
  · intro h
    exact LinearMap.mem_ker.mpr
      ((ker_W_fold x y p.1 p.2 hx hx2 hxy hLart).mpr (LinearMap.mem_ker.mp h))

/-- **THE FOLD LAW, numeric form.** dim ker W_{m+1} = dim ker W_m + 2^m
at every left-alternative rung. -/
theorem finrank_ker_W_fold {m : ℕ} (x y : CD m)
    (hx : conj x = neg x) (hx2 : x * x = neg (cdOne : CD m))
    (hxy : y * x = neg (x * y))
    (hLart : ∀ u w : CD m, u * (u * w) = (u * u) * w) :
    Module.finrank ℝ (LinearMap.ker (WT x y))
      = Module.finrank ℝ (LinearMap.ker (WA x y)) + 2 ^ m := by
  have h1 := ker_WTP_eq x y hx hx2 hxy hLart
  have h2 : LinearMap.range ((WA x y).comp (LinearMap.fst ℝ (CD m) (CD m)))
      = LinearMap.range (WA x y) := by
    ext v
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p.1, hp⟩
    · rintro ⟨a, ha⟩
      exact ⟨(a, (cdZero : CD m)), ha⟩
  have h3 := LinearMap.finrank_range_add_finrank_ker
    ((WA x y).comp (LinearMap.fst ℝ (CD m) (CD m)))
  have h4 := LinearMap.finrank_range_add_finrank_ker (WA x y)
  rw [h2, Module.finrank_prod, finrank_cd] at h3
  rw [finrank_cd] at h4
  have h5 : LinearMap.range (WTP x y) = LinearMap.range (WT x y) := by
    ext v
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨cdPairLm p, hp⟩
    · rintro ⟨u, hu⟩
      obtain ⟨p, hp⟩ := cdPairLm_surjective u
      exact ⟨p, by
        have hg : WT x y (cdPairLm p) = v := by rw [hp]; exact hu
        exact hg⟩
  have h6 := LinearMap.finrank_range_add_finrank_ker (WTP x y)
  have h7 := LinearMap.finrank_range_add_finrank_ker (WT x y)
  rw [h5, Module.finrank_prod, finrank_cd] at h6
  rw [finrank_cd, pow_succ, Nat.mul_two] at h7
  rw [h1] at h6
  omega

/-- **Base rung: the ℍ anti-associator is injective** (step 5: W(a) = 0
forces a = 0, and W is linear). -/
theorem WA_quaternion_injective : Function.Injective (WA unitI unitJ) := by
  intro a b h
  have h1 : WA unitI unitJ (a - b) = (cdZero : CD 2) := by
    rw [LinearMap.map_sub, h, sub_self]
  have h2 : (unitI * (a - b)) * unitJ + unitI * ((a - b) * unitJ) = (cdZero : CD 2) := h1
  exact sub_eq_zero (W_inj_quaternion (a - b) h2)

/-- **The 16-census value 4, machine-checked.** dim ker W(i, j)|𝕆 = 4:
the fold law at the ℍ→𝕆 rung, 0 + 2^2. -/
theorem finrank_ker_WT_octonion :
    Module.finrank ℝ (LinearMap.ker (WT unitI unitJ)) = 4 := by
  rw [finrank_ker_W_fold unitI unitJ conj_unitI unitI_sq hxy_units art_left_two]
  have hE := LinearEquiv.finrank_eq
    (LinearEquiv.ofInjective (WA unitI unitJ) WA_quaternion_injective)
  have hR := LinearMap.finrank_range_add_finrank_ker (WA unitI unitJ)
  rw [← hE] at hR
  have hK : Module.finrank ℝ (LinearMap.ker (WA unitI unitJ)) = 0 := by omega
  rw [hK]
  decide

/-- **Embedded quaternion units at level 3.** The pair (i, j) sitting
inside the octonions satisfies the same anticommuting-imaginary
hypotheses at level 3, with left art there. -/
theorem conj_unitI' : conj ((dbl unitI (cdZero : CD 2)) : CD 3)
    = neg (dbl unitI (cdZero : CD 2)) := by
  show dbl (conj unitI) (neg (cdZero : CD 2)) = neg (dbl unitI (cdZero : CD 2))
  rw [conj_unitI, neg_dbl]

theorem unitI_sq' : ((dbl unitI (cdZero : CD 2)) : CD 3) * (dbl unitI (cdZero : CD 2))
    = neg (cdOne : CD 3) := by
  show dbl (unitI * unitI - (cdZero : CD 2) * conj (cdZero : CD 2))
      (conj unitI * (cdZero : CD 2) + unitI * (cdZero : CD 2))
    = neg (dbl (cdOne : CD 2) (cdZero : CD 2))
  rw [zero_mul, sub_zero, mul_zero, mul_zero, add_zero, unitI_sq, neg_dbl, neg_zero]

theorem hxy_units' : ((dbl unitJ (cdZero : CD 2)) : CD 3) * (dbl unitI (cdZero : CD 2))
    = neg ((dbl unitI (cdZero : CD 2)) * (dbl unitJ (cdZero : CD 2))) := by
  show dbl (unitJ * unitI - (cdZero : CD 2) * conj (cdZero : CD 2))
      (conj unitJ * (cdZero : CD 2) + unitI * (cdZero : CD 2))
    = neg (dbl (unitI * unitJ - (cdZero : CD 2) * conj (cdZero : CD 2))
      (conj unitI * (cdZero : CD 2) + unitJ * (cdZero : CD 2)))
  rw [zero_mul, sub_zero, mul_zero, mul_zero, add_zero,
    sub_zero, mul_zero, mul_zero, add_zero,
    hxy_units, neg_dbl, neg_zero]

/-- **The 32-census value 12, machine-checked.** dim ker W(i', j')|S = 12:
the fold law at the 𝕆→S rung, 4 + 2^3, where the level-3 kernel is the
level-2 doubled kernel by `WA_eq_WT_embed`. -/
theorem finrank_ker_WT_sedenion :
    Module.finrank ℝ (LinearMap.ker (WT (dbl unitI (cdZero : CD 2))
      (dbl unitJ (cdZero : CD 2)))) = 12 := by
  rw [finrank_ker_W_fold (dbl unitI (cdZero : CD 2)) (dbl unitJ (cdZero : CD 2))
      conj_unitI' unitI_sq' hxy_units' art_left_three,
    WA_eq_WT_embed, finrank_ker_WT_octonion]
  decide

/-!
### Basis units: left and right art at every level

Full left alternativity dies at the sedenions, and it dies in exactly one
lemma of the chain: `art_left_lin`, which polarises the art onto the sum
x + y. A single basis unit never needs that. Every standard basis element
is built by doubling a lower basis element into the lower or the upper
slot, and both the left art x(xw) = (xx)w and the right art (wx)x = w(xx)
pass to the next level using only the two arts of that one lower unit.
The real unit is 1; every other basis unit is imaginary, with square −1.
-/

/-- Standard basis of the Cayley–Dickson tower. `real0` is 1 at level 0;
`lower` embeds a basis unit as (u, 0); `upper` embeds it as (0, u). -/
inductive BasisUnit : {m : ℕ} → CD m → Prop
  | real0 : BasisUnit (cdOne : CD 0)
  | lower {m : ℕ} {u : CD m} (hu : BasisUnit u) :
      BasisUnit (dbl u (cdZero : CD m))
  | upper {m : ℕ} {u : CD m} (hu : BasisUnit u) :
      BasisUnit (dbl (cdZero : CD m) u)

theorem basisUnit_cdOne (m : ℕ) : BasisUnit (cdOne : CD m) := by
  induction m with
  | zero => exact BasisUnit.real0
  | succ _ ih => exact BasisUnit.lower ih

/-- The pack carried by every basis unit: it is 1, or it is imaginary of
square −1; and it is left-alternative and right-alternative on the whole
algebra of its level. -/
theorem basisUnit_pack {m : ℕ} {x : CD m} (hx : BasisUnit x) :
    (x = (cdOne : CD m) ∨ (conj x = neg x ∧ x * x = neg (cdOne : CD m))) ∧
    (∀ w : CD m, x * (x * w) = (x * x) * w) ∧
    (∀ w : CD m, (w * x) * x = w * (x * x)) := by
  induction hx with
  | real0 =>
    refine ⟨Or.inl rfl, ?_, ?_⟩
    · intro w
      cases w with
      | zero r =>
        show zero (1 * (1 * r)) = zero ((1 * 1) * r)
        exact congrArg zero (by ring)
    · intro w
      cases w with
      | zero r =>
        show zero ((r * 1) * 1) = zero (r * (1 * 1))
        exact congrArg zero (by ring)
  | @lower m u hu ih =>
    obtain ⟨hkind, ihL, ihR⟩ := ih
    rcases hkind with h1 | hIm
    · subst h1
      refine ⟨Or.inl rfl, ?_, ?_⟩
      · intro w
        change (cdOne : CD (m + 1)) * ((cdOne : CD (m + 1)) * w)
          = ((cdOne : CD (m + 1)) * (cdOne : CD (m + 1))) * w
        rw [one_mul, one_mul, one_mul, one_mul]
      · intro w
        change (w * (cdOne : CD (m + 1))) * (cdOne : CD (m + 1))
          = w * ((cdOne : CD (m + 1)) * (cdOne : CD (m + 1)))
        rw [mul_one, mul_one, mul_one, mul_one]
    · obtain ⟨hconj, hsq⟩ := hIm
      have hconjx : conj (dbl u (cdZero : CD m)) = neg (dbl u (cdZero : CD m)) := by
        show dbl (conj u) (neg (cdZero : CD m)) = neg (dbl u (cdZero : CD m))
        rw [hconj, neg_dbl]
      have hsqx : dbl u (cdZero : CD m) * dbl u (cdZero : CD m)
          = neg (cdOne : CD (m + 1)) := by
        show dbl (u * u - (cdZero : CD m) * conj (cdZero : CD m))
            (conj u * (cdZero : CD m) + u * (cdZero : CD m))
          = neg (dbl (cdOne : CD m) (cdZero : CD m))
        rw [zero_mul, sub_zero, mul_zero, mul_zero, add_zero, hsq, neg_dbl, neg_zero]
      refine ⟨Or.inr ⟨hconjx, hsqx⟩, ?_, ?_⟩
      · intro w
        cases w with
        | dbl a b =>
          have inner : dbl u (cdZero : CD m) * dbl a b = dbl (u * a) (conj u * b) := by
            show dbl (u * a - b * conj (cdZero : CD m))
                (conj u * b + a * (cdZero : CD m))
              = dbl (u * a) (conj u * b)
            rw [conj_zero, mul_zero, sub_zero, mul_zero, add_zero]
          have outer : dbl u (cdZero : CD m) * dbl (u * a) (conj u * b)
              = dbl (u * (u * a)) (conj u * (conj u * b)) := by
            show dbl (u * (u * a) - (conj u * b) * conj (cdZero : CD m))
                (conj u * (conj u * b) + (u * a) * (cdZero : CD m))
              = dbl (u * (u * a)) (conj u * (conj u * b))
            rw [conj_zero, mul_zero, sub_zero, mul_zero, add_zero]
          have rhs : neg (cdOne : CD (m + 1)) * dbl a b = dbl (neg a) (neg b) := by
            rw [neg_mul, one_mul, neg_dbl]
          have hc1 : u * (u * a) = neg a := by
            rw [ihL a, hsq, neg_mul, one_mul]
          have hc2 : conj u * (conj u * b) = neg b := by
            rw [hconj, neg_mul, neg_mul, mul_neg, neg_neg, ihL b, hsq, neg_mul, one_mul]
          rw [inner, outer, hsqx, rhs, hc1, hc2]
      · intro w
        cases w with
        | dbl a b =>
          have inner : dbl a b * dbl u (cdZero : CD m) = dbl (a * u) (u * b) := by
            show dbl (a * u - (cdZero : CD m) * conj b) (conj a * (cdZero : CD m) + u * b)
              = dbl (a * u) (u * b)
            rw [zero_mul, sub_zero, mul_zero, zero_add]
          have outer : dbl (a * u) (u * b) * dbl u (cdZero : CD m)
              = dbl ((a * u) * u) (u * (u * b)) := by
            show dbl ((a * u) * u - (cdZero : CD m) * conj (u * b))
                (conj (a * u) * (cdZero : CD m) + u * (u * b))
              = dbl ((a * u) * u) (u * (u * b))
            rw [zero_mul, sub_zero, mul_zero, zero_add]
          have xsq : dbl u (cdZero : CD m) * dbl u (cdZero : CD m)
              = dbl (u * u) (cdZero : CD m) := by
            show dbl (u * u - (cdZero : CD m) * conj (cdZero : CD m))
                (conj u * (cdZero : CD m) + u * (cdZero : CD m))
              = dbl (u * u) (cdZero : CD m)
            rw [zero_mul, sub_zero, mul_zero, mul_zero, add_zero]
          have rhs : dbl a b * dbl (u * u) (cdZero : CD m)
              = dbl (a * (u * u)) ((u * u) * b) := by
            show dbl (a * (u * u) - (cdZero : CD m) * conj b)
                (conj a * (cdZero : CD m) + (u * u) * b)
              = dbl (a * (u * u)) ((u * u) * b)
            rw [zero_mul, sub_zero, mul_zero, zero_add]
          rw [inner, outer, xsq, rhs, ihR a, ihL b]
  | @upper m u hu ih =>
    obtain ⟨hkind, ihL, ihR⟩ := ih
    have hunorm : u * conj u = (cdOne : CD m) := by
      rcases hkind with h1 | hIm
      · rw [h1, conj_one, mul_one]
      · rw [hIm.1, mul_neg, hIm.2, neg_neg]
    have hconjx : conj (dbl (cdZero : CD m) u) = neg (dbl (cdZero : CD m) u) := by
      show dbl (conj (cdZero : CD m)) (neg u) = neg (dbl (cdZero : CD m) u)
      rw [conj_zero, neg_dbl, neg_zero]
    have hsqx : dbl (cdZero : CD m) u * dbl (cdZero : CD m) u
        = neg (cdOne : CD (m + 1)) := by
      show dbl ((cdZero : CD m) * (cdZero : CD m) - u * conj u)
          (conj (cdZero : CD m) * u + (cdZero : CD m) * u)
        = neg (dbl (cdOne : CD m) (cdZero : CD m))
      rw [zero_mul, hunorm, sub_add, zero_add, conj_zero, zero_mul, add_zero,
        neg_dbl, neg_zero]
    refine ⟨Or.inr ⟨hconjx, hsqx⟩, ?_, ?_⟩
    · intro w
      cases w with
      | dbl a b =>
        have inner : dbl (cdZero : CD m) u * dbl a b
            = dbl (neg (b * conj u)) (a * u) := by
          show dbl ((cdZero : CD m) * a - b * conj u)
              (conj (cdZero : CD m) * b + a * u)
            = dbl (neg (b * conj u)) (a * u)
          rw [zero_mul, sub_add, zero_add, conj_zero, zero_mul, zero_add]
        have outer : dbl (cdZero : CD m) u * dbl (neg (b * conj u)) (a * u)
            = dbl (neg ((a * u) * conj u)) (neg ((b * conj u) * u)) := by
          show dbl ((cdZero : CD m) * neg (b * conj u) - (a * u) * conj u)
              (conj (cdZero : CD m) * (a * u) + neg (b * conj u) * u)
            = dbl (neg ((a * u) * conj u)) (neg ((b * conj u) * u))
          rw [zero_mul, sub_add, zero_add, conj_zero, zero_mul, zero_add, neg_mul]
        have rhs : neg (cdOne : CD (m + 1)) * dbl a b = dbl (neg a) (neg b) := by
          rw [neg_mul, one_mul, neg_dbl]
        have hc1 : (a * u) * conj u = a := by
          rcases hkind with h1 | hIm
          · rw [h1, conj_one, mul_one, mul_one]
          · rw [hIm.1, mul_neg, ihR a, hIm.2, mul_neg, mul_one, neg_neg]
        have hc2 : (b * conj u) * u = b := by
          rcases hkind with h1 | hIm
          · rw [h1, conj_one, mul_one, mul_one]
          · rw [hIm.1, mul_neg, neg_mul, ihR b, hIm.2, mul_neg, mul_one, neg_neg]
        rw [inner, outer, hsqx, rhs, hc1, hc2]
    · intro w
      cases w with
      | dbl a b =>
        have inner : dbl a b * dbl (cdZero : CD m) u
            = dbl (neg (u * conj b)) (conj a * u) := by
          show dbl (a * (cdZero : CD m) - u * conj b)
              (conj a * u + (cdZero : CD m) * b)
            = dbl (neg (u * conj b)) (conj a * u)
          rw [mul_zero, sub_add, zero_add, zero_mul, add_zero]
        have outer : dbl (neg (u * conj b)) (conj a * u) * dbl (cdZero : CD m) u
            = dbl (neg (u * (conj u * a))) (neg ((b * conj u) * u)) := by
          show dbl (neg (u * conj b) * (cdZero : CD m) - u * conj (conj a * u))
              (conj (neg (u * conj b)) * u + (cdZero : CD m) * (conj a * u))
            = dbl (neg (u * (conj u * a))) (neg ((b * conj u) * u))
          rw [mul_zero, sub_add, zero_add, conj_mul, conj_conj, conj_neg, zero_mul,
            add_zero, conj_mul, conj_conj, neg_mul]
        have hc1 : u * (conj u * a) = a := by
          rcases hkind with h1 | hIm
          · rw [h1, conj_one, one_mul, one_mul]
          · rw [hIm.1, neg_mul, mul_neg, ihL a, hIm.2, neg_mul, one_mul, neg_neg]
        have hc2 : (b * conj u) * u = b := by
          rcases hkind with h1 | hIm
          · rw [h1, conj_one, mul_one, mul_one]
          · rw [hIm.1, mul_neg, neg_mul, ihR b, hIm.2, mul_neg, mul_one, neg_neg]
        rw [inner, outer, hsqx, hc1, hc2, mul_neg, mul_one, neg_dbl]

theorem basisUnit_left_art {m : ℕ} {x : CD m} (hx : BasisUnit x) (w : CD m) :
    x * (x * w) = (x * x) * w :=
  (basisUnit_pack hx).2.1 w

theorem basisUnit_right_art {m : ℕ} {x : CD m} (hx : BasisUnit x) (w : CD m) :
    (w * x) * x = w * (x * x) :=
  (basisUnit_pack hx).2.2 w

/-!
### Basis infrastructure, floor 1: signs and anticommutativity

1 is never its own negation; conjugation fixes or negates every basis
unit; and distinct imaginary basis units anticommute — all by induction
on the tower, with no coordinates and no alternativity.
-/

/-- 1 is never its own negation: characteristic zero at every level. -/
theorem cdOne_ne_neg_one {m : ℕ} : (cdOne : CD m) ≠ neg (cdOne : CD m) := by
  induction m with
  | zero =>
    intro h
    have h1 : zero (1 : ℝ) = zero (-1 : ℝ) := h
    injection h1 with h2
    norm_num at h2
  | succ n ih =>
    intro h
    have h' : dbl (cdOne : CD n) (cdZero : CD n)
        = dbl (neg (cdOne : CD n)) (neg (cdZero : CD n)) := h
    injection h' with hidx h1 h2
    exact ih h1

/-- `cdZero` subtracts as negation (Mathlib's `zero_sub` is about `Zero.zero). -/
theorem cdZero_sub {m : ℕ} (a : CD m) : (cdZero : CD m) - a = neg a := by
  rw [sub_add, zero_add]

/-- Conjugation of a lower unit determines the subunit. -/
theorem conj_lower {n : ℕ} {u : CD n}
    (h : conj (dbl u (cdZero : CD n)) = neg (dbl u (cdZero : CD n))) :
    conj u = neg u := by
  have h' : dbl (conj u) (neg (cdZero : CD n))
      = dbl (neg u) (neg (cdZero : CD n)) := by
    rw [← neg_dbl]
    exact h
  exact congrArg Prod.fst (congrArg cdUnpair h')

/-- Conjugation fixes or negates every basis unit. -/
theorem basisUnit_conj {m : ℕ} {x : CD m} (hx : BasisUnit x) :
    conj x = x ∨ conj x = neg x := by
  induction hx with
  | real0 => exact Or.inl conj_one
  | @lower n u hu ih =>
    rcases ih with h | h
    · exact Or.inl (by
        show dbl (conj u) (neg (cdZero : CD n)) = dbl u (cdZero : CD n)
        rw [h, neg_zero])
    · exact Or.inr (by
        show dbl (conj u) (neg (cdZero : CD n)) = neg (dbl u (cdZero : CD n))
        rw [h, neg_dbl])
  | @upper n u hu ih =>
    exact Or.inr (by
      show dbl (conj (cdZero : CD n)) (neg u) = neg (dbl (cdZero : CD n) u)
      rw [conj_zero, neg_dbl, neg_zero])

/-- Distinct imaginary basis units anticommute, at every level. -/
theorem basisUnit_anticomm {m : ℕ} {x y : CD m} (hx : BasisUnit x) (hy : BasisUnit y)
    (hImx : conj x = neg x) (hImy : conj y = neg y) (hne : x ≠ y) :
    y * x = neg (x * y) := by
  induction hx with
  | real0 =>
    rw [conj_one] at hImx
    exact absurd hImx cdOne_ne_neg_one
  | @lower n u hu ih =>
    cases hy with
    | @lower _ v hv =>
      have hcu : conj u = neg u := conj_lower hImx
      have hcv : conj v = neg v := conj_lower hImy
      have hne_uv : u ≠ v := fun hcon => hne (by rw [hcon])
      have e : v * u = neg (u * v) := ih hv hcu hcv hne_uv
      show dbl (v * u - (cdZero : CD n) * conj (cdZero : CD n))
          (conj v * (cdZero : CD n) + u * (cdZero : CD n))
        = neg (dbl (u * v - (cdZero : CD n) * conj (cdZero : CD n))
          (conj u * (cdZero : CD n) + v * (cdZero : CD n)))
      simp only [zero_mul, sub_zero, mul_zero, add_zero, neg_dbl, neg_zero, e]
    | @upper _ v hv =>
      have hcu : conj u = neg u := conj_lower hImx
      show dbl ((cdZero : CD n) * u - (cdZero : CD n) * conj v)
          (conj (cdZero : CD n) * (cdZero : CD n) + u * v)
        = neg (dbl (u * (cdZero : CD n) - v * conj (cdZero : CD n))
          (conj u * v + (cdZero : CD n) * (cdZero : CD n)))
      simp only [conj_zero, zero_mul, mul_zero, sub_zero, add_zero, zero_add,
        neg_dbl, neg_zero, hcu, neg_mul, neg_neg]
  | @upper n u hu ih =>
    cases hy with
    | @lower _ v hv =>
      have hcv : conj v = neg v := conj_lower hImy
      show dbl (v * (cdZero : CD n) - u * conj (cdZero : CD n))
          (conj v * u + (cdZero : CD n) * (cdZero : CD n))
        = neg (dbl ((cdZero : CD n) * v - (cdZero : CD n) * conj u)
          (conj (cdZero : CD n) * (cdZero : CD n) + v * u))
      simp only [conj_zero, zero_mul, mul_zero, sub_zero, add_zero, zero_add,
        neg_dbl, neg_zero, hcv, neg_mul]
    | @upper _ v hv =>
      rcases (basisUnit_pack hu).1 with rfl | ⟨hcu, -⟩
      · rcases (basisUnit_pack hv).1 with rfl | ⟨hcv, -⟩
        · simp at hne
        · show dbl ((cdZero : CD n) * (cdZero : CD n)
                - (cdOne : CD n) * conj v)
              (conj (cdZero : CD n) * (cdOne : CD n)
                + (cdZero : CD n) * v)
            = neg (dbl ((cdZero : CD n) * (cdZero : CD n)
                - v * conj (cdOne : CD n))
              (conj (cdZero : CD n) * v
                + (cdZero : CD n) * (cdOne : CD n)))
          simp only [conj_zero, conj_one, zero_mul, mul_zero, one_mul, mul_one,
            add_zero, neg_dbl, neg_zero, cdZero_sub, neg_neg, hcv]
      · rcases (basisUnit_pack hv).1 with rfl | ⟨hcv, -⟩
        · show dbl ((cdZero : CD n) * (cdZero : CD n)
                - u * conj (cdOne : CD n))
              (conj (cdZero : CD n) * u
                + (cdZero : CD n) * (cdOne : CD n))
            = neg (dbl ((cdZero : CD n) * (cdZero : CD n)
                - (cdOne : CD n) * conj u)
              (conj (cdZero : CD n) * (cdOne : CD n)
                + (cdZero : CD n) * u))
          simp only [conj_zero, conj_one, zero_mul, mul_zero, one_mul, mul_one,
            add_zero, neg_dbl, neg_zero, cdZero_sub, neg_neg, hcu]
        · have hne_uv : u ≠ v := fun hcon => hne (by rw [hcon])
          have e : v * u = neg (u * v) := ih hv hcu hcv hne_uv
          show dbl ((cdZero : CD n) * (cdZero : CD n) - u * conj v)
              (conj (cdZero : CD n) * u
                + (cdZero : CD n) * v)
            = neg (dbl ((cdZero : CD n) * (cdZero : CD n) - v * conj u)
              (conj (cdZero : CD n) * v
                + (cdZero : CD n) * u))
          simp only [conj_zero, zero_mul, mul_zero, add_zero,
            neg_dbl, neg_zero, cdZero_sub, neg_neg, hcu, hcv, mul_neg,
            e]

/-!
### Basis infrastructure, floor 2: signed closure

Products of basis units stay basis up to sign. The induction is on the
level (complete at every rung), since upper-lower products need the full
level-below hypothesis with the factors swapped.
-/

/-- Products of basis units stay basis up to sign, by level induction. -/
theorem basisUnit_mul_closed_aux : ∀ (m : ℕ) (x y : CD m),
    BasisUnit x → BasisUnit y →
    ∃ z, BasisUnit z ∧ (x * y = z ∨ x * y = neg z) := by
  intro m
  induction m with
  | zero =>
    intro x y hx hy
    cases hx with
    | real0 =>
      cases hy with
      | real0 => exact ⟨cdOne, BasisUnit.real0, Or.inl (mul_one _)⟩
  | succ n ih =>
    intro x y hx hy
    cases hx with
    | @lower _ u hu =>
      cases hy with
      | @lower _ v hv =>
        have pLL : dbl u (cdZero : CD n) * dbl v (cdZero : CD n)
            = dbl (u * v) (cdZero : CD n) := by
          show dbl (u * v - (cdZero : CD n) * conj (cdZero : CD n))
              (conj u * (cdZero : CD n) + v * (cdZero : CD n))
            = dbl (u * v) (cdZero : CD n)
          simp only [zero_mul, sub_zero, mul_zero, add_zero]
        obtain ⟨w, hw, h | h⟩ := ih u v hu hv
        · exact ⟨dbl w (cdZero : CD n), BasisUnit.lower hw, Or.inl (by rw [pLL, h])⟩
        · exact ⟨dbl w (cdZero : CD n), BasisUnit.lower hw,
            Or.inr (by rw [pLL, h, neg_dbl, neg_zero])⟩
      | @upper _ v hv =>
        have pLU : dbl u (cdZero : CD n) * dbl (cdZero : CD n) v
            = dbl (cdZero : CD n) (conj u * v) := by
          show dbl (u * (cdZero : CD n) - v * conj (cdZero : CD n))
              (conj u * v + (cdZero : CD n) * (cdZero : CD n))
            = dbl (cdZero : CD n) (conj u * v)
          simp only [mul_zero, conj_zero, sub_zero, add_zero]
        rcases basisUnit_conj hu with hc | hc
        · obtain ⟨w, hw, h | h⟩ := ih u v hu hv
          · exact ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw,
              Or.inl (by rw [pLU, hc, h])⟩
          · exact ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw,
              Or.inr (by rw [pLU, hc, h, neg_dbl, neg_zero])⟩
        · obtain ⟨w, hw, h | h⟩ := ih u v hu hv
          · exact ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw,
              Or.inr (by rw [pLU, hc, neg_mul, h, neg_dbl, neg_zero])⟩
          · exact ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw,
              Or.inl (by rw [pLU, hc, neg_mul, h, neg_neg])⟩
    | @upper _ u hu =>
      cases hy with
      | @lower _ v hv =>
        have pUL : dbl (cdZero : CD n) u * dbl v (cdZero : CD n)
            = dbl (cdZero : CD n) (v * u) := by
          show dbl ((cdZero : CD n) * v - (cdZero : CD n) * conj u)
              (conj (cdZero : CD n) * (cdZero : CD n) + v * u)
            = dbl (cdZero : CD n) (v * u)
          simp only [conj_zero, zero_mul, mul_zero, sub_zero, zero_add]
        obtain ⟨w, hw, h | h⟩ := ih v u hv hu
        · exact ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw,
            Or.inl (by rw [pUL, h])⟩
        · exact ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw,
            Or.inr (by rw [pUL, h, neg_dbl, neg_zero])⟩
      | @upper _ v hv =>
        have pUU : dbl (cdZero : CD n) u * dbl (cdZero : CD n) v
            = dbl (neg (v * conj u)) (cdZero : CD n) := by
          show dbl ((cdZero : CD n) * (cdZero : CD n) - v * conj u)
              (conj (cdZero : CD n) * v
                + (cdZero : CD n) * u)
            = dbl (neg (v * conj u)) (cdZero : CD n)
          simp only [zero_mul, mul_zero, conj_zero, add_zero,
            cdZero_sub]
        rcases basisUnit_conj hu with hc | hc
        · obtain ⟨w, hw, h | h⟩ := ih v u hv hu
          · exact ⟨dbl w (cdZero : CD n), BasisUnit.lower hw,
              Or.inr (by rw [pUU, hc, h, neg_dbl, neg_zero])⟩
          · exact ⟨dbl w (cdZero : CD n), BasisUnit.lower hw,
              Or.inl (by rw [pUU, hc, h, neg_neg])⟩
        · obtain ⟨w, hw, h | h⟩ := ih v u hv hu
          · exact ⟨dbl w (cdZero : CD n), BasisUnit.lower hw,
              Or.inl (by rw [pUU, hc, mul_neg, neg_neg, h])⟩
          · exact ⟨dbl w (cdZero : CD n), BasisUnit.lower hw,
              Or.inr (by rw [pUU, hc, mul_neg, neg_neg, h, neg_dbl, neg_zero])⟩

/-- Products of basis units stay basis up to sign. -/
theorem basisUnit_mul_closed {m : ℕ} {x y : CD m} (hx : BasisUnit x) (hy : BasisUnit y) :
    ∃ z, BasisUnit z ∧ (x * y = z ∨ x * y = neg z) :=
  basisUnit_mul_closed_aux m x y hx hy

/-!
### Basis infrastructure, floor 3: fresh triple products
-/

/-- No basis unit is zero. -/
theorem basisUnit_ne_zero {m : ℕ} {x : CD m} (hx : BasisUnit x) :
    x ≠ (cdZero : CD m) := by
  induction hx with
  | real0 =>
    intro h
    have h1 : zero (1 : ℝ) = zero 0 := h
    injection h1 with h2
    norm_num at h2
  | @lower n u hu ih =>
    intro h
    have h' : dbl u (cdZero : CD n) = dbl (cdZero : CD n) (cdZero : CD n) := h
    injection h' with hidx h1 h2
    exact ih h1
  | @upper n u hu ih =>
    intro h
    have h' : dbl (cdZero : CD n) u = dbl (cdZero : CD n) (cdZero : CD n) := h
    injection h' with hidx h1 h2
    exact ih h2

/-- The lower and upper slots never meet. -/
theorem lower_ne_upper {n : ℕ} {u v : CD n}
    (h1 : u ≠ (cdZero : CD n)) (h2 : v ≠ (cdZero : CD n)) :
    dbl u (cdZero : CD n) ≠ dbl (cdZero : CD n) v := by
  intro hcon
  have h' : dbl u (cdZero : CD n) = dbl (cdZero : CD n) v := hcon
  injection h' with hidx e1 e2
  exact h1 e1

/-- Products of distinct imaginary basis units, by level induction: the
product lands on a FRESH imaginary basis unit up to sign — never ±1,
never either factor. -/
theorem basisUnit_mul_distinct_aux :
    ∀ (m : ℕ) (u v : CD m), BasisUnit u → BasisUnit v →
      conj u = neg u → conj v = neg v → u ≠ v →
      ∃ w, BasisUnit w ∧ conj w = neg w ∧ w ≠ u ∧ w ≠ v ∧
        (u * v = w ∨ u * v = neg w) := by
  intro m
  induction m with
  | zero =>
    intro u v hu hv hcu hcv hne
    cases hu
    rw [conj_one] at hcu
    exact absurd hcu cdOne_ne_neg_one
  | succ n ih =>
    intro u v hu hv hcu hcv hne
    cases hu with
    | @lower _ a ha =>
      have hca : conj a = neg a := conj_lower hcu
      cases hv with
      | @lower _ b hb =>
        have hcb : conj b = neg b := conj_lower hcv
        have hab : a ≠ b := fun hcon => hne (by rw [hcon])
        have pLL : dbl a (cdZero : CD n) * dbl b (cdZero : CD n)
            = dbl (a * b) (cdZero : CD n) := by
          show dbl (a * b - (cdZero : CD n) * conj (cdZero : CD n))
              (conj a * (cdZero : CD n) + b * (cdZero : CD n))
            = dbl (a * b) (cdZero : CD n)
          simp only [zero_mul, sub_zero, mul_zero, add_zero]
        obtain ⟨w, hw, hcw, hwa, hwb, h | h⟩ := ih a b ha hb hca hcb hab
        · refine ⟨dbl w (cdZero : CD n), BasisUnit.lower hw, ?_, ?_, ?_, Or.inl ?_⟩
          · show dbl (conj w) (neg (cdZero : CD n)) = neg (dbl w (cdZero : CD n))
            rw [hcw, neg_dbl]
          · intro hcon
            exact hwa (congrArg Prod.fst (congrArg cdUnpair hcon))
          · intro hcon
            exact hwb (congrArg Prod.fst (congrArg cdUnpair hcon))
          · rw [pLL, h]
        · refine ⟨dbl w (cdZero : CD n), BasisUnit.lower hw, ?_, ?_, ?_, Or.inr ?_⟩
          · show dbl (conj w) (neg (cdZero : CD n)) = neg (dbl w (cdZero : CD n))
            rw [hcw, neg_dbl]
          · intro hcon
            exact hwa (congrArg Prod.fst (congrArg cdUnpair hcon))
          · intro hcon
            exact hwb (congrArg Prod.fst (congrArg cdUnpair hcon))
          · rw [pLL, h, neg_dbl, neg_zero]
      | @upper _ b hb =>
        have pLU : dbl a (cdZero : CD n) * dbl (cdZero : CD n) b
            = dbl (cdZero : CD n) (conj a * b) := by
          show dbl (a * (cdZero : CD n) - b * conj (cdZero : CD n))
              (conj a * b + (cdZero : CD n) * (cdZero : CD n))
            = dbl (cdZero : CD n) (conj a * b)
          simp only [mul_zero, conj_zero, zero_mul, sub_self, add_zero]
        rcases (basisUnit_pack hb).1 with rfl | ⟨hcb, -⟩
        · refine ⟨dbl (cdZero : CD n) a, BasisUnit.upper ha, ?_, ?_, ?_, Or.inr ?_⟩
          · show dbl (conj (cdZero : CD n)) (neg a) = neg (dbl (cdZero : CD n) a)
            rw [conj_zero, neg_dbl, neg_zero]
          · intro hcon
            exact (basisUnit_ne_zero ha)
              (congrArg Prod.fst (congrArg cdUnpair hcon)).symm
          · intro hcon
            have e : a = (cdOne : CD n) :=
              congrArg Prod.snd (congrArg cdUnpair hcon)
            rw [e, conj_one] at hca
            exact absurd hca cdOne_ne_neg_one
          · rw [pLU, mul_one, hca, neg_dbl, neg_zero]
        · rcases eq_or_ne a b with hab | hab
          · have hsa : a * a = neg (cdOne : CD n) := by
              rcases (basisUnit_pack ha).1 with hreal | ⟨-, hs⟩
              · rw [hreal, conj_one] at hca
                exact absurd hca cdOne_ne_neg_one
              · exact hs
            refine ⟨dbl (cdZero : CD n) (cdOne : CD n),
              BasisUnit.upper (basisUnit_cdOne n), ?_, ?_, ?_, Or.inl ?_⟩
            · show dbl (conj (cdZero : CD n)) (neg (cdOne : CD n))
                = neg (dbl (cdZero : CD n) (cdOne : CD n))
              rw [conj_zero, neg_dbl, neg_zero]
            · intro hcon
              exact (basisUnit_ne_zero ha)
                (congrArg Prod.fst (congrArg cdUnpair hcon)).symm
            · intro hcon
              have e : (cdOne : CD n) = b :=
                congrArg Prod.snd (congrArg cdUnpair hcon)
              have ea : a = (cdOne : CD n) := hab.trans e.symm
              rw [ea, conj_one] at hca
              exact absurd hca cdOne_ne_neg_one
            · rw [pLU, ← hab, hca, neg_mul, hsa, neg_neg]
          · obtain ⟨w, hw, hcw, hwa, hwb, h | h⟩ := ih a b ha hb hca hcb hab
            · refine ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw, ?_, ?_, ?_, Or.inr ?_⟩
              · show dbl (conj (cdZero : CD n)) (neg w)
                  = neg (dbl (cdZero : CD n) w)
                rw [conj_zero, neg_dbl, neg_zero]
              · intro hcon
                exact (basisUnit_ne_zero ha)
                  (congrArg Prod.fst (congrArg cdUnpair hcon)).symm
              · intro hcon
                exact hwb (congrArg Prod.snd (congrArg cdUnpair hcon))
              · rw [pLU, hca, neg_mul, h, neg_dbl, neg_zero]
            · refine ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw, ?_, ?_, ?_, Or.inl ?_⟩
              · show dbl (conj (cdZero : CD n)) (neg w)
                  = neg (dbl (cdZero : CD n) w)
                rw [conj_zero, neg_dbl, neg_zero]
              · intro hcon
                exact (basisUnit_ne_zero ha)
                  (congrArg Prod.fst (congrArg cdUnpair hcon)).symm
              · intro hcon
                exact hwb (congrArg Prod.snd (congrArg cdUnpair hcon))
              · rw [pLU, hca, neg_mul, h, neg_neg]
    | @upper _ a ha =>
      cases hv with
      | @lower _ b hb =>
        have hcb : conj b = neg b := conj_lower hcv
        have pUL : dbl (cdZero : CD n) a * dbl b (cdZero : CD n)
            = dbl (cdZero : CD n) (b * a) := by
          show dbl ((cdZero : CD n) * b - (cdZero : CD n) * conj a)
              (conj (cdZero : CD n) * (cdZero : CD n) + b * a)
            = dbl (cdZero : CD n) (b * a)
          simp only [conj_zero, zero_mul, sub_zero, zero_add]
        rcases (basisUnit_pack ha).1 with rfl | ⟨hca, hsa⟩
        · refine ⟨dbl (cdZero : CD n) b, BasisUnit.upper hb, ?_, ?_, ?_, Or.inl ?_⟩
          · show dbl (conj (cdZero : CD n)) (neg b) = neg (dbl (cdZero : CD n) b)
            rw [conj_zero, neg_dbl, neg_zero]
          · intro hcon
            have e : b = (cdOne : CD n) :=
              congrArg Prod.snd (congrArg cdUnpair hcon)
            rw [e, conj_one] at hcb
            exact absurd hcb cdOne_ne_neg_one
          · intro hcon
            exact (basisUnit_ne_zero hb)
              (congrArg Prod.fst (congrArg cdUnpair hcon)).symm
          · rw [pUL, mul_one]
        · rcases eq_or_ne a b with hab | hab
          · refine ⟨dbl (cdZero : CD n) (cdOne : CD n),
              BasisUnit.upper (basisUnit_cdOne n), ?_, ?_, ?_, Or.inr ?_⟩
            · show dbl (conj (cdZero : CD n)) (neg (cdOne : CD n))
                = neg (dbl (cdZero : CD n) (cdOne : CD n))
              rw [conj_zero, neg_dbl, neg_zero]
            · intro hcon
              have e : (cdOne : CD n) = a :=
                congrArg Prod.snd (congrArg cdUnpair hcon)
              rw [← e, conj_one] at hca
              exact absurd hca cdOne_ne_neg_one
            · intro hcon
              exact (basisUnit_ne_zero hb)
                (congrArg Prod.fst (congrArg cdUnpair hcon)).symm
            · rw [pUL, ← hab, hsa, neg_dbl, neg_zero]
          · obtain ⟨w, hw, hcw, hwb, hwa, h | h⟩ := ih b a hb ha hcb hca (Ne.symm hab)
            · refine ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw, ?_, ?_, ?_, Or.inl ?_⟩
              · show dbl (conj (cdZero : CD n)) (neg w)
                  = neg (dbl (cdZero : CD n) w)
                rw [conj_zero, neg_dbl, neg_zero]
              · intro hcon
                exact hwa (congrArg Prod.snd (congrArg cdUnpair hcon))
              · intro hcon
                exact (basisUnit_ne_zero hb)
                  (congrArg Prod.fst (congrArg cdUnpair hcon)).symm
              · rw [pUL, h]
            · refine ⟨dbl (cdZero : CD n) w, BasisUnit.upper hw, ?_, ?_, ?_, Or.inr ?_⟩
              · show dbl (conj (cdZero : CD n)) (neg w)
                  = neg (dbl (cdZero : CD n) w)
                rw [conj_zero, neg_dbl, neg_zero]
              · intro hcon
                exact hwa (congrArg Prod.snd (congrArg cdUnpair hcon))
              · intro hcon
                exact (basisUnit_ne_zero hb)
                  (congrArg Prod.fst (congrArg cdUnpair hcon)).symm
              · rw [pUL, h, neg_dbl, neg_zero]
      | @upper _ b hb =>
        have hab : a ≠ b := fun hcon => hne (by rw [hcon])
        have pUU : dbl (cdZero : CD n) a * dbl (cdZero : CD n) b
            = dbl (neg (b * conj a)) (cdZero : CD n) := by
          show dbl ((cdZero : CD n) * (cdZero : CD n) - b * conj a)
              (conj (cdZero : CD n) * b + (cdZero : CD n) * a)
            = dbl (neg (b * conj a)) (cdZero : CD n)
          simp only [zero_mul, conj_zero, cdZero_sub, add_zero]
        rcases (basisUnit_pack ha).1 with rfl | ⟨hca, -⟩
        · rcases (basisUnit_pack hb).1 with rfl | ⟨hcb, -⟩
          · exact (hne rfl).elim
          · refine ⟨dbl b (cdZero : CD n), BasisUnit.lower hb, ?_, ?_, ?_, Or.inr ?_⟩
            · show dbl (conj b) (neg (cdZero : CD n)) = neg (dbl b (cdZero : CD n))
              rw [hcb, neg_dbl]
            · intro hcon
              exact (basisUnit_ne_zero hb)
                (congrArg Prod.fst (congrArg cdUnpair hcon))
            · intro hcon
              exact (basisUnit_ne_zero hb)
                (congrArg Prod.fst (congrArg cdUnpair hcon))
            · rw [pUU, conj_one, mul_one, neg_dbl, neg_zero]
        · rcases (basisUnit_pack hb).1 with rfl | ⟨hcb, -⟩
          · refine ⟨dbl a (cdZero : CD n), BasisUnit.lower ha, ?_, ?_, ?_, Or.inl ?_⟩
            · show dbl (conj a) (neg (cdZero : CD n)) = neg (dbl a (cdZero : CD n))
              rw [hca, neg_dbl]
            · intro hcon
              exact (basisUnit_ne_zero ha)
                (congrArg Prod.fst (congrArg cdUnpair hcon))
            · intro hcon
              exact (basisUnit_ne_zero ha)
                (congrArg Prod.fst (congrArg cdUnpair hcon))
            · rw [pUU, one_mul, hca, neg_neg]
          · obtain ⟨w, hw, hcw, hwb, hwa, h | h⟩ := ih b a hb ha hcb hca (Ne.symm hab)
            · refine ⟨dbl w (cdZero : CD n), BasisUnit.lower hw, ?_, ?_, ?_, Or.inl ?_⟩
              · show dbl (conj w) (neg (cdZero : CD n)) = neg (dbl w (cdZero : CD n))
                rw [hcw, neg_dbl]
              · intro hcon
                exact (basisUnit_ne_zero hw)
                  (congrArg Prod.fst (congrArg cdUnpair hcon))
              · intro hcon
                exact (basisUnit_ne_zero hw)
                  (congrArg Prod.fst (congrArg cdUnpair hcon))
              · rw [pUU, hca, mul_neg, neg_neg, h]
            · refine ⟨dbl w (cdZero : CD n), BasisUnit.lower hw, ?_, ?_, ?_, Or.inr ?_⟩
              · show dbl (conj w) (neg (cdZero : CD n)) = neg (dbl w (cdZero : CD n))
                rw [hcw, neg_dbl]
              · intro hcon
                exact (basisUnit_ne_zero hw)
                  (congrArg Prod.fst (congrArg cdUnpair hcon))
              · intro hcon
                exact (basisUnit_ne_zero hw)
                  (congrArg Prod.fst (congrArg cdUnpair hcon))
              · rw [pUU, hca, mul_neg, neg_neg, h, neg_dbl, neg_zero]

/-- Products of distinct imaginary basis units land on a fresh
imaginary basis unit, up to sign. -/
theorem basisUnit_mul_distinct {m : ℕ} {u v : CD m}
    (hu : BasisUnit u) (hv : BasisUnit v)
    (hcu : conj u = neg u) (hcv : conj v = neg v) (hne : u ≠ v) :
    ∃ w, BasisUnit w ∧ conj w = neg w ∧ w ≠ u ∧ w ≠ v ∧
      (u * v = w ∨ u * v = neg w) :=
  basisUnit_mul_distinct_aux m u v hu hv hcu hcv hne

/-!
### Basis infrastructure, floor 3½: the cancellation laws

If x·u lands on ±y then u is already the third quaternion unit ±w.
This is the cancellation the H^⊥-invariance of W will need: fresh
products can never collapse back onto the quaternion axes. Only unit
art, no alternativity, no coordinates.
-/

/-- −1 multiplies as negation on the left, at every level. -/
theorem neg_one_mul {m : ℕ} (a : CD m) : neg (cdOne : CD m) * a = neg a := by
  rw [neg_mul, one_mul]

/-- Right multiplication by −1 is negation, at every level. -/
theorem mul_neg_one {m : ℕ} (a : CD m) : a * neg (cdOne : CD m) = neg a := by
  rw [mul_neg, mul_one]

/-- Negation is injective at every level. -/
theorem neg_inj {m : ℕ} {a b : CD m} (h : neg a = neg b) : a = b := by
  have h2 := congrArg neg h
  rw [neg_neg, neg_neg] at h2
  exact h2

/-- An imaginary basis unit squares to −1. -/
theorem basisUnit_sq {m : ℕ} {x : CD m} (hx : BasisUnit x) (hcx : conj x = neg x) :
    x * x = neg (cdOne : CD m) := by
  rcases (basisUnit_pack hx).1 with hreal | ⟨-, hs⟩
  · rw [hreal, conj_one] at hcx
    exact absurd hcx cdOne_ne_neg_one
  · exact hs

/-- Core cancellation: if x·y = ±w and x·y = −u, then u = ±w. -/
theorem basisUnit_cancel_core {m : ℕ} {x y u w : CD m}
    (hxy : x * y = w ∨ x * y = neg w) (h1 : x * y = neg u) :
    u = w ∨ u = neg w := by
  rcases hxy with hw | hw
  · rw [hw] at h1
    exact Or.inr (by rw [h1, neg_neg])
  · exact Or.inl (by rw [← neg_neg u, ← (hw.symm.trans h1), neg_neg])

/-- Left cancellation: if x·u lands on ±y then u = ±w, where w is the
fresh unit carried by x·y. -/
theorem basisUnit_cancel_left {m : ℕ} {x y u w : CD m}
    (hx : BasisUnit x) (hcx : conj x = neg x)
    (hxy : x * y = w ∨ x * y = neg w)
    (h : x * u = y ∨ x * u = neg y) :
    u = w ∨ u = neg w := by
  have hart : x * (x * u) = neg u := by
    rw [basisUnit_left_art hx u, basisUnit_sq hx hcx, neg_one_mul]
  rcases h with h | h
  · rw [h] at hart
    exact basisUnit_cancel_core hxy hart
  · rw [h, mul_neg] at hart
    have e : u = x * y := (neg_inj hart).symm
    rcases hxy with hw | hw
    · rw [hw] at e; exact Or.inl e
    · rw [hw] at e; exact Or.inr e

/-- Right cancellation: if u·y lands on ±x then u = ±w. -/
theorem basisUnit_cancel_right {m : ℕ} {x y u w : CD m}
    (hy : BasisUnit y) (hcy : conj y = neg y)
    (hxy : x * y = w ∨ x * y = neg w)
    (h : u * y = x ∨ u * y = neg x) :
    u = w ∨ u = neg w := by
  have hart : (u * y) * y = neg u := by
    rw [basisUnit_right_art hy u, basisUnit_sq hy hcy, mul_neg_one]
  rcases h with h | h
  · rw [h] at hart
    exact basisUnit_cancel_core hxy hart
  · rw [h, neg_mul] at hart
    have e : u = x * y := (neg_inj hart).symm
    rcases hxy with hw | hw
    · rw [hw] at e; exact Or.inl e
    · rw [hw] at e; exact Or.inr e

/-- Companion: the third unit of the quaternion (x, y) sends w back to
±y under x. -/
theorem basisUnit_xw {m : ℕ} {x y w : CD m}
    (hx : BasisUnit x) (hcx : conj x = neg x)
    (hxy : x * y = w ∨ x * y = neg w) :
    x * w = y ∨ x * w = neg y := by
  have hart : x * (x * y) = neg y := by
    rw [basisUnit_left_art hx y, basisUnit_sq hx hcx, neg_one_mul]
  rcases hxy with hw | hw
  · rw [hw] at hart
    exact Or.inr hart
  · rw [hw, mul_neg] at hart
    exact Or.inl (neg_inj hart)

/-- Companion: w sends y back to ±x on the right. -/
theorem basisUnit_wy {m : ℕ} {x y w : CD m}
    (hy : BasisUnit y) (hcy : conj y = neg y)
    (hxy : x * y = w ∨ x * y = neg w) :
    w * y = x ∨ w * y = neg x := by
  have hart : (x * y) * y = neg x := by
    rw [basisUnit_right_art hy x, basisUnit_sq hy hcy, mul_neg_one]
  rcases hxy with hw | hw
  · rw [hw] at hart
    exact Or.inr hart
  · rw [hw, neg_mul] at hart
    exact Or.inl (neg_inj hart)

/-- Companion: y sends w back to ±x. -/
theorem basisUnit_yw {m : ℕ} {x y w : CD m}
    (hx : BasisUnit x) (hcx : conj x = neg x)
    (hy : BasisUnit y) (hcy : conj y = neg y) (hne : x ≠ y)
    (hxy : x * y = w ∨ x * y = neg w) :
    y * w = x ∨ y * w = neg x := by
  have hanti : y * x = neg (x * y) := basisUnit_anticomm hx hy hcx hcy hne
  rcases hxy with hw | hw
  · rw [hw] at hanti
    rcases basisUnit_xw hy hcy (Or.inl hanti) with h2 | h2
    · rw [mul_neg] at h2
      refine Or.inr ?_
      have h3 := congrArg neg h2
      rw [neg_neg] at h3
      exact h3
    · rw [mul_neg] at h2
      exact Or.inl (neg_inj h2)
  · rw [hw] at hanti
    rcases basisUnit_xw hy hcy (Or.inr hanti) with h2 | h2
    · rw [mul_neg] at h2
      refine Or.inr ?_
      have h3 := congrArg neg h2
      rw [neg_neg] at h3
      exact h3
    · rw [mul_neg] at h2
      exact Or.inl (neg_inj h2)

/-!
### Basis infrastructure, floor 4: the data layer

`BasisUnit` is a proposition; linear combinations need an index that
carries data. `BUnit` mirrors it as a Type, `beval` evaluates it into
the tower, and the two are tight: every basis unit is hit
(`basisUnit_beval`) and `beval` is injective (`beval_inj`), so the
family has no repeats. The successor level splits as lower ⊕ upper
(`bUnitSuccEquiv`), which makes the family finite with exactly 2^m
members (`bUnit_card`) — the spine the linear layer (independence,
basis, H^⊥ spans) will hang from.
-/

/-- Data-level index for the standard basis of the tower. -/
inductive BUnit : ℕ → Type
  | real0 : BUnit 0
  | lower {m : ℕ} (u : BUnit m) : BUnit (m + 1)
  | upper {m : ℕ} (u : BUnit m) : BUnit (m + 1)
  deriving DecidableEq

/-- The evaluation of a data unit: the corresponding tower element. -/
def beval : ∀ {m : ℕ}, BUnit m → CD m
  | 0, BUnit.real0 => cdOne
  | m + 1, BUnit.lower u => dbl (beval u) (cdZero : CD m)
  | m + 1, BUnit.upper u => dbl (cdZero : CD m) (beval u)

/-- Every data unit evaluates to a basis unit. -/
theorem beval_basis {m : ℕ} (u : BUnit m) : BasisUnit (beval u) := by
  induction u with
  | real0 => exact basisUnit_cdOne 0
  | @lower n v ih => exact BasisUnit.lower ih
  | @upper n v ih => exact BasisUnit.upper ih

/-- `beval` is injective: distinct data units give distinct elements. -/
theorem beval_inj : ∀ (m : ℕ) (u v : BUnit m), beval u = beval v → u = v := by
  intro m
  induction m with
  | zero =>
    intro u v h
    cases u with
    | real0 =>
      cases v with
      | real0 => rfl
  | succ n ih =>
    intro u v h
    cases u with
    | lower u' =>
      cases v with
      | lower v' =>
        have h' : dbl (beval u') (cdZero : CD n) = dbl (beval v') (cdZero : CD n) := h
        injection h' with hidx h1 h2
        exact congrArg BUnit.lower (ih u' v' h1)
      | upper v' =>
        have h' : dbl (beval u') (cdZero : CD n)
            = dbl (cdZero : CD n) (beval v') := h
        exact absurd h' (lower_ne_upper (basisUnit_ne_zero (beval_basis u'))
          (basisUnit_ne_zero (beval_basis v')))
    | upper u' =>
      cases v with
      | lower v' =>
        have h' : dbl (cdZero : CD n) (beval u')
            = dbl (beval v') (cdZero : CD n) := h
        exact absurd h' (Ne.symm (lower_ne_upper (basisUnit_ne_zero (beval_basis v'))
          (basisUnit_ne_zero (beval_basis u'))))
      | upper v' =>
        have h' : dbl (cdZero : CD n) (beval u') = dbl (cdZero : CD n) (beval v') := h
        injection h' with hidx h1 h2
        exact congrArg BUnit.upper (ih u' v' h2)

/-- Every basis unit is hit by a data unit. -/
theorem basisUnit_beval {m : ℕ} {x : CD m} (hx : BasisUnit x) :
    ∃ u : BUnit m, beval u = x := by
  induction hx with
  | real0 => exact ⟨BUnit.real0, rfl⟩
  | @lower n v hv ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨BUnit.lower u, ?_⟩
    show dbl (beval u) (cdZero : CD n) = dbl v (cdZero : CD n)
    exact congrArg (fun z => dbl z (cdZero : CD n)) hu
  | @upper n v hv ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨BUnit.upper u, ?_⟩
    show dbl (cdZero : CD n) (beval u) = dbl (cdZero : CD n) v
    exact congrArg (fun z => dbl (cdZero : CD n) z) hu

/-- The successor level splits as the lower and upper copies. -/
def bUnitSuccEquiv (m : ℕ) : BUnit (m + 1) ≃ BUnit m ⊕ BUnit m where
  toFun i :=
    match i with
    | BUnit.lower u => Sum.inl u
    | BUnit.upper u => Sum.inr u
  invFun s :=
    match s with
    | Sum.inl u => BUnit.lower u
    | Sum.inr u => BUnit.upper u
  left_inv i := by cases i <;> rfl
  right_inv s := by cases s <;> rfl

instance bUnitFintype (m : ℕ) : Fintype (BUnit m) := by
  induction m with
  | zero =>
    exact ⟨{BUnit.real0}, by intro u; cases u; simp⟩
  | succ n ih =>
    exact Fintype.ofEquiv (BUnit n ⊕ BUnit n) (bUnitSuccEquiv n).symm

/-- The family has exactly 2^m members. -/
theorem bUnit_card (m : ℕ) : Fintype.card (BUnit m) = 2 ^ m := by
  induction m with
  | zero => decide
  | succ n ih =>
    rw [Fintype.card_congr (bUnitSuccEquiv n), Fintype.card_sum, ih,
      ← Nat.mul_two, ← pow_succ]

/-!
### Floor 4, step B: linear independence of the unit family

The unit family `beval : BUnit m → CD m` is linearly independent. The
proof runs by level induction; the successor step partitions the sum
over `BUnit (n+1)` into lower and upper halves via the successor
equivalence, pulls each half through the doubling, and reads off the
two components. Together with `bUnit_card` this turns the family into
a genuine basis (step C), which is what the H/H^⊥ decomposition
downstream needs.
-/

/-- Zero self-adds to zero (a direct instance of `add_zero`). -/
theorem cdZero_add_cdZero {m : ℕ} : (cdZero : CD m) + cdZero = cdZero :=
  add_zero cdZero

/-- The instance-level copy of `smul_zero`. -/
theorem smul_zero' {m : ℕ} (r : ℝ) : r • (cdZero : CD m) = cdZero := smul_zero r

/-- Scalars pass through the doubling (index has succ shape: defeq). -/
theorem smul_dbl {m : ℕ} (r : ℝ) (x y : CD m) :
    r • (dbl x y : CD (m + 1)) = dbl (r • x) (r • y) := rfl

/-- Instance-level copies of the scalar-passes-through multiplication
lemmas: they bridge the `cdSmul` lemmas to the `•` notation, by defeq. -/
theorem smul_mul_left' {m : ℕ} (r : ℝ) (a b : CD m) :
    (r • a) * b = r • (a * b) := smul_mul_left r a b

theorem smul_mul_right' {m : ℕ} (r : ℝ) (a b : CD m) :
    a * (r • b) = r • (a * b) := smul_mul_right r a b

theorem smul_add'' {m : ℕ} (r : ℝ) (a b : CD m) :
    r • (a + b) = r • a + r • b := smul_add' r a b

/-- Finite sums pass through the CD multiplication on the left. -/
theorem cd_sum_mul_left {m : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → CD m) (y : CD m) :
    (∑ i ∈ s, f i) * y = ∑ i ∈ s, f i * y := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact zero_mul y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mul', ih]

/-- Finite sums pass through the CD multiplication on the right. -/
theorem cd_sum_mul_right {m : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (y : CD m) (f : ι → CD m) :
    y * (∑ i ∈ s, f i) = ∑ i ∈ s, y * f i := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact mul_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, mul_add', ih]

/-- Doubling into the lower slot, as an additive homomorphism. -/
def dblLowerHom {m : ℕ} : CD m →+ CD (m + 1) where
  toFun z := dbl z (cdZero : CD m)
  map_zero' := rfl
  map_add' a b := by
    have hsum : (a, (cdZero : CD m)) + (b, cdZero) = (a + b, cdZero) := by
      show (a + b, (cdZero : CD m) + cdZero) = (a + b, cdZero)
      rw [cdZero_add_cdZero]
    have h := cdPairLm.map_add (a, cdZero) (b, cdZero)
    rw [hsum] at h
    exact h

/-- Doubling into the upper slot, as an additive homomorphism. -/
def dblUpperHom {m : ℕ} : CD m →+ CD (m + 1) where
  toFun z := dbl (cdZero : CD m) z
  map_zero' := rfl
  map_add' a b := by
    have hsum : ((cdZero : CD m), a) + (cdZero, b) = (cdZero, a + b) := by
      show ((cdZero : CD m) + cdZero, a + b) = (cdZero, a + b)
      rw [cdZero_add_cdZero]
    have h := cdPairLm.map_add (cdZero, a) (cdZero, b)
    rw [hsum] at h
    exact h

/-- Sums of lower doubles pass through the doubling. -/
theorem sum_dbl_lower {m : ℕ} (f : BUnit m → CD m) :
    (∑ u : BUnit m, dbl (f u) (cdZero : CD m))
      = dbl (∑ u : BUnit m, f u) (cdZero : CD m) :=
  (map_sum dblLowerHom f Finset.univ).symm

/-- Sums of upper doubles pass through the doubling. -/
theorem sum_dbl_upper {m : ℕ} (f : BUnit m → CD m) :
    (∑ u : BUnit m, dbl (cdZero : CD m) (f u))
      = dbl (cdZero : CD m) (∑ u : BUnit m, f u) :=
  (map_sum dblUpperHom f Finset.univ).symm

/-- A sum over the lower units collapses to the lower slot. -/
theorem sum_lower_split {m : ℕ} (g : BUnit (m + 1) → ℝ) :
    (∑ u : BUnit m, g (BUnit.lower u) • beval (BUnit.lower u))
      = dbl (∑ u : BUnit m, g (BUnit.lower u) • beval u) (cdZero : CD m) := by
  rw [Finset.sum_congr rfl (fun u _ => by
    show g (BUnit.lower u) • (dbl (beval u) (cdZero : CD m))
      = dbl (g (BUnit.lower u) • beval u) (cdZero : CD m)
    rw [smul_dbl, smul_zero']), sum_dbl_lower _]

/-- A sum over the upper units collapses to the upper slot. -/
theorem sum_upper_split {m : ℕ} (g : BUnit (m + 1) → ℝ) :
    (∑ u : BUnit m, g (BUnit.upper u) • beval (BUnit.upper u))
      = dbl (cdZero : CD m) (∑ u : BUnit m, g (BUnit.upper u) • beval u) := by
  rw [Finset.sum_congr rfl (fun u _ => by
    show g (BUnit.upper u) • (dbl (cdZero : CD m) (beval u))
      = dbl (cdZero : CD m) (g (BUnit.upper u) • beval u)
    rw [smul_dbl, smul_zero']), sum_dbl_upper _]

instance : Unique (BUnit 0) where
  default := BUnit.real0
  uniq a := by cases a; rfl

/-- Independence, by level induction. -/
theorem beval_linearIndependent_aux : ∀ (m : ℕ) (g : BUnit m → ℝ),
    (∑ i : BUnit m, g i • beval i) = (cdZero : CD m) → ∀ i : BUnit m, g i = 0 := by
  intro m
  induction m with
  | zero =>
    intro g hg i
    cases i with
    | real0 =>
      have h1 : (∑ i : BUnit 0, g i • beval i)
          = g BUnit.real0 • beval BUnit.real0 :=
        Finset.sum_eq_single BUnit.real0
          (fun b _ hb => by cases b; exact absurd rfl hb)
          (fun h => absurd (Finset.mem_univ BUnit.real0) h)
      rw [h1] at hg
      have h' : zero ((g BUnit.real0) * 1) = zero 0 := hg
      injection h' with h2
      rw [_root_.mul_one] at h2
      exact h2
  | succ n ih =>
    intro g hg
    have hsplit : (∑ i : BUnit (n + 1), g i • beval i)
        = (∑ u : BUnit n, g (BUnit.lower u) • beval (BUnit.lower u))
          + (∑ u : BUnit n, g (BUnit.upper u) • beval (BUnit.upper u)) := by
      calc (∑ i : BUnit (n + 1), g i • beval i)
          = (∑ s : BUnit n ⊕ BUnit n, (fun j : BUnit (n + 1) => g j • beval j)
              ((bUnitSuccEquiv n).symm s)) :=
            Fintype.sum_equiv (bUnitSuccEquiv n)
              (fun j : BUnit (n + 1) => g j • beval j)
              (fun s : BUnit n ⊕ BUnit n =>
                g ((bUnitSuccEquiv n).symm s) • beval ((bUnitSuccEquiv n).symm s))
              (fun j => by cases j <;> rfl)
        _ = (∑ u : BUnit n, g (BUnit.lower u) • beval (BUnit.lower u))
            + (∑ u : BUnit n, g (BUnit.upper u) • beval (BUnit.upper u)) :=
            Fintype.sum_sum_type
              (fun s : BUnit n ⊕ BUnit n =>
                g ((bUnitSuccEquiv n).symm s) • beval ((bUnitSuccEquiv n).symm s))
    rw [hsplit, sum_lower_split, sum_upper_split] at hg
    have h' : dbl ((∑ u : BUnit n, g (BUnit.lower u) • beval u) + (cdZero : CD n))
        ((cdZero : CD n) + (∑ u : BUnit n, g (BUnit.upper u) • beval u))
      = (cdZero : CD (n + 1)) := hg
    have hfst : (∑ u : BUnit n, g (BUnit.lower u) • beval u) + (cdZero : CD n)
        = (cdZero : CD n) := congrArg Prod.fst (congrArg cdUnpair h')
    have hsnd : (cdZero : CD n) + (∑ u : BUnit n, g (BUnit.upper u) • beval u)
        = (cdZero : CD n) := congrArg Prod.snd (congrArg cdUnpair h')
    rw [add_zero] at hfst
    rw [zero_add] at hsnd
    intro i
    cases i with
    | lower u => exact ih (fun v => g (BUnit.lower v)) hfst u
    | upper u => exact ih (fun v => g (BUnit.upper v)) hsnd u

/-- The unit family is linearly independent. -/
theorem beval_linearIndependent {m : ℕ} :
    LinearIndependent ℝ (beval : BUnit m → CD m) :=
  Fintype.linearIndependent_iff.mpr (fun g hg => beval_linearIndependent_aux m g hg)

/-- The unit one is never zero. -/
theorem cdOne_ne_zero {m : ℕ} : (cdOne : CD m) ≠ cdZero := by
  induction m with
  | zero =>
    intro h
    have h' : zero (1:ℝ) = zero 0 := h
    injection h' with h1
    exact one_ne_zero h1
  | succ n ih =>
    intro h
    have h' : dbl (cdOne : CD n) (cdZero : CD n)
        = dbl (cdZero : CD n) (cdZero : CD n) := h
    injection h' with hidx h1 h2
    exact ih h1

instance cdNontrivial {m : ℕ} : Nontrivial (CD m) :=
  ⟨cdZero, cdOne, fun h => cdOne_ne_zero h.symm⟩

/-- The unit family is a basis of the tower: independent, and the
count 2^m matches the rank. -/
noncomputable def bevalBasis (m : ℕ) : Module.Basis (BUnit m) ℝ (CD m) :=
  basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) beval beval_linearIndependent
    (by rw [bUnit_card, finrank_cd])

/-!
### Floor 5, step A: freshness infrastructure

The H^⊥ machinery needs one more structural fact about the index set:
no two basis units sit on the same line (`beval_neg_inj`), so an
imaginary unit and its negative are never both basis units
(`basisUnit_neg_not`). On top of that, the two gates every fresh unit
must pass: a fresh unit anticommutes with y (`fresh_anticomm`), and
x sends fresh indices to fresh indices up to sign (`fresh_mul_left`),
with the ±w branch closed by cancellation and the line lemma.
-/

/-- Two basis units never sit on the same line. -/
theorem beval_neg_inj : ∀ (m : ℕ) (u v : BUnit m),
    beval u = neg (beval v) → u = v := by
  intro m
  induction m with
  | zero =>
    intro u v h
    cases u with
    | real0 =>
      cases v with
      | real0 => exact (cdOne_ne_neg_one h).elim
  | succ n ih =>
    intro u v h
    cases u with
    | lower u' =>
      cases v with
      | lower v' =>
        have h1 : dbl (beval u') (cdZero : CD n)
            = neg (dbl (beval v') (cdZero : CD n)) := h
        rw [neg_dbl, neg_zero] at h1
        injection h1 with hidx hc1 hc2
        exact congrArg BUnit.lower (ih u' v' hc1)
      | upper v' =>
        have h1 : dbl (beval u') (cdZero : CD n)
            = neg (dbl (cdZero : CD n) (beval v')) := h
        rw [neg_dbl, neg_zero] at h1
        have hneg : neg (beval v') ≠ (cdZero : CD n) := by
          intro hc
          have h2 := congrArg neg hc
          rw [neg_neg, neg_zero] at h2
          exact basisUnit_ne_zero (beval_basis v') h2
        exact absurd h1 (lower_ne_upper (basisUnit_ne_zero (beval_basis u')) hneg)
    | upper u' =>
      cases v with
      | lower v' =>
        have h1 : dbl (cdZero : CD n) (beval u')
            = neg (dbl (beval v') (cdZero : CD n)) := h
        rw [neg_dbl, neg_zero] at h1
        have hneg : neg (beval v') ≠ (cdZero : CD n) := by
          intro hc
          have h2 := congrArg neg hc
          rw [neg_neg, neg_zero] at h2
          exact basisUnit_ne_zero (beval_basis v') h2
        exact absurd h1 (Ne.symm (lower_ne_upper hneg
          (basisUnit_ne_zero (beval_basis u'))))
      | upper v' =>
        have h1 : dbl (cdZero : CD n) (beval u')
            = neg (dbl (cdZero : CD n) (beval v')) := h
        rw [neg_dbl, neg_zero] at h1
        injection h1 with hidx hc1 hc2
        exact congrArg BUnit.upper (ih u' v' hc2)

/-- An imaginary unit and its negative are never both basis units:
the index set meets each line exactly once. -/
theorem basisUnit_neg_not {m : ℕ} {z w : CD m}
    (hz : BasisUnit z) (hw : BasisUnit w) (h : z = -w) : False := by
  obtain ⟨u, hu⟩ := basisUnit_beval hz
  obtain ⟨v, hv⟩ := basisUnit_beval hw
  have hne : beval u = neg (beval v) :=
    hu.trans (h.trans (congrArg neg hv.symm))
  have huv : u = v := beval_neg_inj m u v hne
  have hzw : z = w := by rw [← hu, ← hv, huv]
  rw [hzw] at h
  -- now h : w = -w, so 2 • w = 0, and over ℝ this forces w = 0
  have h9 : w + w = (0 : CD m) := by
    have h10 : w + w = w + neg w := congrArg (fun t : CD m => w + t) h
    rw [add_neg_self] at h10
    exact h10
  have h11 : (2 : ℝ) • w = (0 : CD m) := by rw [two_smul]; exact h9
  have h13 : (2⁻¹ : ℝ) • (2 : ℝ) • w = (2⁻¹ : ℝ) • (0 : CD m) :=
    congrArg ((2⁻¹ : ℝ) • ·) h11
  rw [_root_.smul_zero, inv_smul_smul₀ two_ne_zero] at h13
  exact basisUnit_ne_zero hw h13

/-- Gate A: a unit whose value is neither 1 nor y anticommutes
with y. -/
theorem fresh_anticomm {m : ℕ} (y : CD m) (e1 ey : BUnit m)
    (hby : BasisUnit y) (hcy : conj y = neg y)
    (he1 : beval e1 = (cdOne : CD m)) (hey : beval ey = y)
    (u : BUnit m) (hu1 : u ≠ e1) (huy : u ≠ ey) :
    (beval u) * y + y * (beval u) = (cdZero : CD m) := by
  have hbu : BasisUnit (beval u) := beval_basis u
  have hb1 : beval u ≠ (cdOne : CD m) := by
    intro hc
    exact hu1 (beval_inj m u e1 (hc.trans he1.symm))
  have hne : beval u ≠ y := by
    intro hc
    exact huy (beval_inj m u ey (hc.trans hey.symm))
  rcases (basisUnit_pack hbu).1 with hreal | ⟨hcu, -⟩
  · exact absurd hreal hb1
  · rw [basisUnit_anticomm hbu hby hcu hcy hne, add_neg_self]

/-- Gate B: x sends fresh indices to fresh indices, up to sign. The
±w branch closes by cancellation; the landed-on-y branch would force
u = ±w, and both signs die (u = ew excluded; the negative is not a
unit by the line lemma). -/
theorem fresh_mul_left {m : ℕ} (x y w : CD m) (e1 ex ey ew : BUnit m)
    (hbx : BasisUnit x) (hcx : conj x = neg x)
    (hby : BasisUnit y) (hcy : conj y = neg y)
    (hbw : BasisUnit w) (hne : x ≠ y)
    (hw : x * y = w ∨ x * y = neg w)
    (he1 : beval e1 = (cdOne : CD m)) (hex : beval ex = x)
    (hey : beval ey = y) (hew : beval ew = w)
    (u : BUnit m)
    (hu1 : u ≠ e1) (hux : u ≠ ex) (huy : u ≠ ey) (huw : u ≠ ew) :
    ∃ v : BUnit m, v ≠ e1 ∧ v ≠ ex ∧ v ≠ ey ∧ v ≠ ew ∧
      (x * (beval u) = beval v ∨ x * (beval u) = neg (beval v)) := by
  have hbu : BasisUnit (beval u) := beval_basis u
  have hb1 : beval u ≠ (cdOne : CD m) := by
    intro hc
    exact hu1 (beval_inj m u e1 (hc.trans he1.symm))
  have hcu : conj (beval u) = neg (beval u) := by
    rcases (basisUnit_pack hbu).1 with hreal | ⟨hc, -⟩
    · exact absurd hreal hb1
    · exact hc
  have hxbu : x ≠ beval u := by
    intro hc
    exact hux (beval_inj m u ex (hc.symm.trans hex.symm))
  obtain ⟨w', hw'bu, hcw', hw'x, hw'u, hprod⟩ :=
    basisUnit_mul_distinct hbx hbu hcx hcu hxbu
  obtain ⟨v, hv⟩ := basisUnit_beval hw'bu
  -- w' ≠ 1 (it is imaginary), so v ≠ e1
  have hw'1 : w' ≠ (cdOne : CD m) := by
    intro hcon
    rw [hcon] at hcw'
    rw [conj_one] at hcw'
    exact cdOne_ne_neg_one hcw'
  refine ⟨v, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon
    exact hw'1 (by rw [← hv, hcon, he1])
  · intro hcon
    exact hw'x (by rw [← hv, hcon, hex])
  · intro hcon
    -- w' = y would force x·(beval u) = ±y, hence beval u = ±w
    have hyl : w' = y := by rw [← hv, hcon, hey]
    rw [hyl] at hprod
    have huw' : beval u = w ∨ beval u = neg w :=
      basisUnit_cancel_left hbx hcx hw hprod
    rcases huw' with hc | hc
    · exact huw (beval_inj m u ew (hc.trans hew.symm))
    · exact basisUnit_neg_not hbu hbw hc
  · intro hcon
    -- w' = w would force x·(beval u) = ±w; multiply by x and use x·w = ±y
    have hwl : w' = w := by rw [← hv, hcon, hew]
    rw [hwl] at hprod
    have hart : x * (x * (beval u)) = neg (beval u) :=
      (basisUnit_pack hbx).2.1 (beval u) |>.trans
        (by rw [basisUnit_sq hbx hcx, neg_one_mul])
    have hxwy : x * w = y ∨ x * w = neg y := basisUnit_xw hbx hcx hw
    rcases hprod with h1 | h1 <;> rcases hxwy with h2 | h2
    · rw [h1, h2] at hart
      have hfin := congrArg neg hart
      rw [neg_neg] at hfin
      exact basisUnit_neg_not hbu hby hfin.symm
    · rw [h1, h2] at hart
      exact huy (beval_inj m u ey ((neg_inj hart).symm.trans hey.symm))
    · rw [h1, mul_neg, h2] at hart
      exact huy (beval_inj m u ey ((neg_inj hart).symm.trans hey.symm))
    · rw [h1, mul_neg, h2, neg_neg] at hart
      have hfin := congrArg neg hart
      rw [neg_neg] at hfin
      exact basisUnit_neg_not hbu hby hfin.symm
  · rw [hv]
    exact hprod

/-!
### Floor 5, step B: the H/fresh decomposition

With `DecidableEq` on the index set, any element splits as the sum of
its four distinguished coordinates (the H-part over {e1, ex, ey, ew})
and its fresh part (the rest of the basis). This is the partition the
H^⊥-invariance of W will be read through.
-/

/-- The basis vectors are literally the evaluated units. -/
theorem bevalBasis_apply (m : ℕ) (i : BUnit m) : bevalBasis m i = beval i :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) beval
    beval_linearIndependent (by rw [bUnit_card, finrank_cd])) i

/-- Any element is its H-part plus its fresh part. -/
theorem a_decomp {m : ℕ} (e1 ex ey ew : BUnit m) (a : CD m) :
    a = (∑ i ∈ ({e1, ex, ey, ew} : Finset (BUnit m)), (bevalBasis m).repr a i • beval i)
      + ∑ i ∈ (Finset.univ \ ({e1, ex, ey, ew} : Finset (BUnit m))),
          (bevalBasis m).repr a i • beval i := by
  have hsr : ∑ i : BUnit m, (bevalBasis m).repr a i • beval i = a := by
    have h := (bevalBasis m).sum_repr a
    simp only [bevalBasis_apply] at h
    exact h
  have h1 : ∑ i ∈ (Finset.univ \ ({e1, ex, ey, ew} : Finset (BUnit m))),
          (bevalBasis m).repr a i • beval i
        + ∑ i ∈ ({e1, ex, ey, ew} : Finset (BUnit m)), (bevalBasis m).repr a i • beval i
      = ∑ i : BUnit m, (bevalBasis m).repr a i • beval i :=
    Finset.sum_sdiff (Finset.subset_univ _)
  rw [add_comm] at h1
  rw [h1]
  exact hsr.symm

/-!
### Floor 5, step C1: right-freshness and the coordinate functionals

`fresh_mul_right` mirrors `fresh_mul_left`: y on the right also sends
fresh indices to fresh indices up to sign. The j-th coordinate is packaged
as the linear functional `coordLm j`; `fresh_W_coord_zero` says W of a
fresh unit has no distinguished component, and `W_coord_split` reads
W(a) through any coordinate j as the four distinguished contributions.
-/

/-- Gate B': y on the right sends fresh indices to fresh indices, up
to sign. -/
theorem fresh_mul_right {m : ℕ} (x y w : CD m) (e1 ex ey ew : BUnit m)
    (hbx : BasisUnit x) (hcx : conj x = neg x)
    (hby : BasisUnit y) (hcy : conj y = neg y)
    (hbw : BasisUnit w) (hne : x ≠ y)
    (hw : x * y = w ∨ x * y = neg w)
    (he1 : beval e1 = (cdOne : CD m)) (hex : beval ex = x)
    (hey : beval ey = y) (hew : beval ew = w)
    (u : BUnit m)
    (hu1 : u ≠ e1) (hux : u ≠ ex) (huy : u ≠ ey) (huw : u ≠ ew) :
    ∃ v : BUnit m, v ≠ e1 ∧ v ≠ ex ∧ v ≠ ey ∧ v ≠ ew ∧
      ((beval u) * y = beval v ∨ (beval u) * y = neg (beval v)) := by
  have hbu : BasisUnit (beval u) := beval_basis u
  have hb1 : beval u ≠ (cdOne : CD m) := by
    intro hc
    exact hu1 (beval_inj m u e1 (hc.trans he1.symm))
  have hcu : conj (beval u) = neg (beval u) := by
    rcases (basisUnit_pack hbu).1 with hreal | ⟨hc, -⟩
    · exact absurd hreal hb1
    · exact hc
  have hyu : beval u ≠ y := by
    intro hc
    exact huy (beval_inj m u ey (hc.trans hey.symm))
  obtain ⟨w', hw'bu, hcw', hw'u, hw'y, hprod⟩ :=
    basisUnit_mul_distinct hbu hby hcu hcy hyu
  obtain ⟨v, hv⟩ := basisUnit_beval hw'bu
  have hw'1 : w' ≠ (cdOne : CD m) := by
    intro hcon
    rw [hcon] at hcw'
    rw [conj_one] at hcw'
    exact cdOne_ne_neg_one hcw'
  refine ⟨v, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon
    exact hw'1 (by rw [← hv, hcon, he1])
  · intro hcon
    -- w' = x would force (beval u)·y = ±x, hence beval u = ±w
    have hxl : w' = x := by rw [← hv, hcon, hex]
    rw [hxl] at hprod
    have huw' : beval u = w ∨ beval u = neg w :=
      basisUnit_cancel_right hby hcy hw hprod
    rcases huw' with hc | hc
    · exact huw (beval_inj m u ew (hc.trans hew.symm))
    · exact basisUnit_neg_not hbu hbw hc
  · intro hcon
    exact hw'y (by rw [← hv, hcon, hey])
  · intro hcon
    -- w' = w would force (beval u)·y = ±w; multiply by y on the right
    have hwl : w' = w := by rw [← hv, hcon, hew]
    rw [hwl] at hprod
    have hart : (beval u * y) * y = neg (beval u) :=
      (basisUnit_pack hby).2.2 (beval u) |>.trans
        (by rw [basisUnit_sq hby hcy, mul_neg_one])
    have hwy : w * y = x ∨ w * y = neg x := basisUnit_wy hby hcy hw
    rcases hprod with h1 | h1 <;> rcases hwy with h2 | h2
    · rw [h1, h2] at hart
      have hfin := congrArg neg hart
      rw [neg_neg] at hfin
      exact basisUnit_neg_not hbu hbx hfin.symm
    · rw [h1, h2] at hart
      exact hux (beval_inj m u ex ((neg_inj hart).symm.trans hex.symm))
    · rw [h1, neg_mul, h2] at hart
      exact hux (beval_inj m u ex ((neg_inj hart).symm.trans hex.symm))
    · rw [h1, neg_mul, h2, neg_neg] at hart
      have hfin := congrArg neg hart
      rw [neg_neg] at hfin
      exact basisUnit_neg_not hbu hbx hfin.symm
  · rw [hv]
    exact hprod

/-- The j-th coordinate, as a linear functional. -/
noncomputable def coordLm {m : ℕ} (j : BUnit m) : CD m →ₗ[ℝ] ℝ :=
  (Finsupp.lapply j).comp ((bevalBasis m).repr.toLinearMap)

/-- The coordinates of a basis unit: 1 at its own index, 0 elsewhere. -/
theorem coord_apply {m : ℕ} (i j : BUnit m) :
    coordLm j (beval i) = if i = j then 1 else 0 := by
  have h1 : coordLm j (beval i)
      = (Finsupp.lapply j : (BUnit m →₀ ℝ) →ₗ[ℝ] ℝ)
          ((bevalBasis m).repr (beval i)) := rfl
  rw [h1, Finsupp.lapply_apply, ← bevalBasis_apply m i]
  exact (bevalBasis m).repr_self_apply i j

/-- Off-diagonal coordinates vanish. -/
theorem coord_val_ne {m : ℕ} (i j : BUnit m) (h : i ≠ j) :
    coordLm j (beval i) = 0 := by
  rw [coord_apply]
  split
  · exact absurd ‹i = j› h
  · rfl

/-- Coordinates commute with the tower negation. -/
theorem coord_neg {m : ℕ} (j : BUnit m) (a : CD m) :
    coordLm j (neg a) = -(coordLm j a) := map_neg _ _

/-- For fresh u, every distinguished coordinate of W(u) vanishes: both
halves of W(u) are fresh units up to sign. -/
theorem fresh_W_coord_zero {m : ℕ} (x y w : CD m) (e1 ex ey ew : BUnit m)
    (hbx : BasisUnit x) (hcx : conj x = neg x)
    (hby : BasisUnit y) (hcy : conj y = neg y)
    (hbw : BasisUnit w) (hne : x ≠ y)
    (hw : x * y = w ∨ x * y = neg w)
    (he1 : beval e1 = (cdOne : CD m)) (hex : beval ex = x)
    (hey : beval ey = y) (hew : beval ew = w)
    (u : BUnit m) (hu1 : u ≠ e1) (hux : u ≠ ex) (huy : u ≠ ey) (huw : u ≠ ew)
    (j : BUnit m) (hj : j = e1 ∨ j = ex ∨ j = ey ∨ j = ew) :
    coordLm j (WA x y (beval u)) = 0 := by
  obtain ⟨v1, h11, h12, h13, h14, hs1⟩ :=
    fresh_mul_left x y w e1 ex ey ew hbx hcx hby hcy hbw hne hw he1 hex hey hew
      u hu1 hux huy huw
  obtain ⟨v2, h21, h22, h23, h24, hs2⟩ :=
    fresh_mul_right x y w e1 ex ey ew hbx hcx hby hcy hbw hne hw he1 hex hey hew
      u hu1 hux huy huw
  have hvj : ∀ v : BUnit m, v ≠ e1 → v ≠ ex → v ≠ ey → v ≠ ew → v ≠ j := by
    intro v h1 h2 h3 h4
    rcases hj with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  obtain ⟨p1, q11, q12, q13, q14, hp1⟩ :=
    fresh_mul_right x y w e1 ex ey ew hbx hcx hby hcy hbw hne hw he1 hex hey hew
      v1 h11 h12 h13 h14
  have ht1 : coordLm j ((x * (beval u)) * y) = 0 := by
    rcases hs1 with h | h <;> rcases hp1 with h' | h'
    · rw [h, h']
      exact coord_val_ne p1 j (hvj p1 q11 q12 q13 q14)
    · rw [h, h', coord_neg, coord_val_ne p1 j (hvj p1 q11 q12 q13 q14),
        _root_.neg_zero]
    · rw [h, neg_mul, h', coord_neg, coord_val_ne p1 j (hvj p1 q11 q12 q13 q14),
        _root_.neg_zero]
    · rw [h, neg_mul, h', coord_neg, coord_neg, _root_.neg_neg,
        coord_val_ne p1 j (hvj p1 q11 q12 q13 q14)]
  obtain ⟨p2, r11, r12, r13, r14, hp2⟩ :=
    fresh_mul_left x y w e1 ex ey ew hbx hcx hby hcy hbw hne hw he1 hex hey hew
      v2 h21 h22 h23 h24
  have ht2 : coordLm j (x * ((beval u) * y)) = 0 := by
    rcases hs2 with h | h <;> rcases hp2 with h' | h'
    · rw [h, h']
      exact coord_val_ne p2 j (hvj p2 r11 r12 r13 r14)
    · rw [h, h', coord_neg, coord_val_ne p2 j (hvj p2 r11 r12 r13 r14),
        _root_.neg_zero]
    · rw [h, mul_neg, h', coord_neg, coord_val_ne p2 j (hvj p2 r11 r12 r13 r14),
        _root_.neg_zero]
    · rw [h, mul_neg, h', coord_neg, coord_neg, _root_.neg_neg,
        coord_val_ne p2 j (hvj p2 r11 r12 r13 r14)]
  show coordLm j ((x * (beval u)) * y + x * ((beval u) * y)) = 0
  rw [map_add, ht1, ht2, _root_.add_zero]

/-- Reading W(a) through the j-th coordinate: only the four
distinguished components survive, with the basis coefficients. -/
theorem W_coord_split {m : ℕ} (x y : CD m) (e1 ex ey ew : BUnit m) (a : CD m)
    (hd1 : e1 ∉ ({ex, ey, ew} : Finset (BUnit m)))
    (hd2 : ex ∉ ({ey, ew} : Finset (BUnit m)))
    (hd3 : ey ∉ ({ew} : Finset (BUnit m)))
    (j : BUnit m)
    (hfresh : ∀ i ∈ (Finset.univ \ ({e1, ex, ey, ew} : Finset (BUnit m))),
       coordLm j ((WA x y) (beval i)) = 0) :
    coordLm j ((WA x y) a)
      = (bevalBasis m).repr a e1 * coordLm j ((WA x y) (beval e1))
      + (bevalBasis m).repr a ex * coordLm j ((WA x y) (beval ex))
      + (bevalBasis m).repr a ey * coordLm j ((WA x y) (beval ey))
      + (bevalBasis m).repr a ew * coordLm j ((WA x y) (beval ew)) := by
  have ha : a = ∑ i : BUnit m, (bevalBasis m).repr a i • beval i := by
    have h := (bevalBasis m).sum_repr a
    simp only [bevalBasis_apply] at h
    exact h.symm
  conv_lhs => rw [ha]
  rw [map_sum (WA x y)]
  rw [map_sum (coordLm j)]
  simp only [map_smul]
  rw [← Finset.sum_sdiff (Finset.subset_univ ({e1, ex, ey, ew} : Finset (BUnit m)))]
  rw [Finset.sum_eq_zero (fun i hi => by rw [hfresh i hi, _root_.smul_zero])]
  rw [_root_.zero_add]
  rw [Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_insert hd3,
    Finset.sum_singleton]
  simp only [smul_eq_mul]
  ring

/-- Embed a unit one level up, in the lower slot: the doubling that builds
the centre family (i, j) at every height. -/
def embed1 {m : ℕ} (x : CD m) : CD (m + 1) := dbl x (cdZero : CD m)

def embedN {m : ℕ} (k : ℕ) (x : CD m) : CD (m + k) :=
  match k with
  | 0 => x
  | k + 1 => embed1 (embedN k x)

theorem conj_imag_embed {m : ℕ} (x : CD m) (h : conj x = neg x) :
    conj (embed1 x) = neg (embed1 x) := by
  unfold embed1
  show dbl (conj x) (neg (cdZero : CD m)) = neg (dbl x (cdZero : CD m))
  rw [h, neg_dbl]

theorem sq_embed {m : ℕ} (x : CD m) (h : x * x = neg (cdOne : CD m)) :
    embed1 x * embed1 x = neg (cdOne : CD (m + 1)) := by
  unfold embed1
  show dbl (x * x - (cdZero : CD m) * conj (cdZero : CD m))
      (conj x * (cdZero : CD m) + x * (cdZero : CD m))
    = neg (dbl (cdOne : CD m) (cdZero : CD m))
  rw [zero_mul, sub_zero, mul_zero, mul_zero, add_zero, h, neg_dbl, neg_zero]

theorem anticomm_embed {m : ℕ} (x y : CD m) (h : y * x = neg (x * y)) :
    embed1 y * embed1 x = neg (embed1 x * embed1 y) := by
  unfold embed1
  show dbl (y * x - (cdZero : CD m) * conj (cdZero : CD m))
      (conj y * (cdZero : CD m) + x * (cdZero : CD m))
    = neg (dbl (x * y - (cdZero : CD m) * conj (cdZero : CD m))
      (conj x * (cdZero : CD m) + y * (cdZero : CD m)))
  rw [zero_mul, sub_zero, mul_zero, mul_zero, add_zero,
    sub_zero, mul_zero, mul_zero, add_zero, h, neg_dbl, neg_zero]

theorem hyxy_embed {m : ℕ} (x y : CD m)
    (h : y * (x * y) = neg ((x * y) * y)) :
    embed1 y * (embed1 x * embed1 y)
      = neg ((embed1 x * embed1 y) * embed1 y) := by
  have hxy : embed1 x * embed1 y = embed1 (x * y) := by
    unfold embed1
    show dbl (x * y - (cdZero : CD m) * conj (cdZero : CD m))
        (conj x * (cdZero : CD m) + y * (cdZero : CD m))
      = dbl (x * y) (cdZero : CD m)
    rw [zero_mul, sub_zero, mul_zero, mul_zero, add_zero]
  rw [hxy]
  unfold embed1
  show dbl (y * (x * y) - (cdZero : CD m) * conj (cdZero : CD m))
      (conj y * (cdZero : CD m) + (x * y) * (cdZero : CD m))
    = neg (dbl ((x * y) * y - (cdZero : CD m) * conj (cdZero : CD m))
      (conj (x * y) * (cdZero : CD m) + y * (cdZero : CD m)))
  rw [zero_mul, sub_zero, mul_zero, mul_zero, add_zero,
    sub_zero, mul_zero, mul_zero, add_zero, h, neg_dbl, neg_zero]

theorem basisUnit_imagI : BasisUnit imagI :=
  BasisUnit.upper (basisUnit_cdOne 0)

theorem basisUnit_unitI : BasisUnit unitI :=
  BasisUnit.lower basisUnit_imagI

theorem basisUnit_unitJ : BasisUnit unitJ :=
  BasisUnit.upper (basisUnit_cdOne 1)

theorem basisUnit_embed1 {m : ℕ} {x : CD m} (hx : BasisUnit x) :
    BasisUnit (embed1 x) :=
  BasisUnit.lower hx

theorem basisUnit_embedN {m : ℕ} (k : ℕ) {x : CD m} (hx : BasisUnit x) :
    BasisUnit (embedN k x) := by
  induction k with
  | zero => exact hx
  | succ _ ih => exact basisUnit_embed1 ih

/-- The quaternion units (i, j), embedded into every higher level, keep
the hypotheses of step (3): imaginary, square −1, anticommuting, the
quaternion relation, and both unit arts. -/
theorem centre_hyp (k : ℕ) :
    conj (embedN k unitI) = neg (embedN k unitI) ∧
    embedN k unitI * embedN k unitI = neg (cdOne : CD (2 + k)) ∧
    conj (embedN k unitJ) = neg (embedN k unitJ) ∧
    embedN k unitJ * embedN k unitJ = neg (cdOne : CD (2 + k)) ∧
    embedN k unitJ * embedN k unitI = neg (embedN k unitI * embedN k unitJ) ∧
    embedN k unitJ * (embedN k unitI * embedN k unitJ)
      = neg ((embedN k unitI * embedN k unitJ) * embedN k unitJ) ∧
    BasisUnit (embedN k unitI) ∧ BasisUnit (embedN k unitJ) := by
  induction k with
  | zero =>
    exact ⟨conj_unitI, unitI_sq, conj_unitJ, unitJ_sq, hxy_units, hyxy_units,
      basisUnit_unitI, basisUnit_unitJ⟩
  | succ n ih =>
    rcases ih with ⟨hx, hx2, hy, hy2, hxy, hyxy, bx, byy⟩
    exact ⟨conj_imag_embed _ hx, sq_embed _ hx2, conj_imag_embed _ hy, sq_embed _ hy2,
      anticomm_embed _ _ hxy, hyxy_embed _ _ hyxy,
      basisUnit_embed1 bx, basisUnit_embed1 byy⟩

/-- **Step (3) for the centre pair, at every level.** H(i, j) sits inside
ker C after any number of lower embeddings. The art used is the unit art
of i and of j, which survives the death of alternativity. -/
theorem C_ker_H_centre (k : ℕ) :
    let x := embedN k unitI
    let y := embedN k unitJ
    y * (conj x * (cdOne : CD (2 + k))) + conj x * (y * (cdOne : CD (2 + k)))
      = (cdZero : CD (2 + k)) ∧
    y * (conj x * x) + conj x * (y * x) = (cdZero : CD (2 + k)) ∧
    y * (conj x * y) + conj x * (y * y) = (cdZero : CD (2 + k)) ∧
    y * (conj x * (x * y)) + conj x * (y * (x * y)) = (cdZero : CD (2 + k)) := by
  intro x y
  rcases centre_hyp k with ⟨hx, hx2, hy, hy2, hxy, hyxy, bx, byy⟩
  exact ⟨C_ker_one x y hx hxy,
    C_ker_x x y hx hx2 hxy (basisUnit_left_art bx),
    C_ker_y x y hx hy2 hyxy (basisUnit_right_art byy),
    C_ker_xy x y hx hx2 hy2 hyxy (basisUnit_left_art bx) (basisUnit_right_art byy)⟩

/-- **C doubles diagonally.** For imaginary x, y embedded in the lower slot,
the complementary block of the embedded pair on (u, v) is (C(u), C(v)).
No alternativity: only conj x = −x and conj y = −y. -/
theorem C_embed {m : ℕ} (x y u v : CD m) (hx : conj x = neg x) (hy : conj y = neg y) :
    dbl y (cdZero : CD m) * (conj (dbl x (cdZero : CD m)) * dbl u v)
      + conj (dbl x (cdZero : CD m)) * (dbl y (cdZero : CD m) * dbl u v)
    = dbl (y * (conj x * u) + conj x * (y * u))
        (y * (conj x * v) + conj x * (y * v)) := by
  have hcx : conj (dbl x (cdZero : CD m)) = dbl (neg x) (cdZero : CD m) := by
    show dbl (conj x) (neg (cdZero : CD m)) = dbl (neg x) (cdZero : CD m)
    rw [hx, neg_zero]
  have h1 : conj (dbl x (cdZero : CD m)) * dbl u v = dbl (neg (x * u)) (x * v) := by
    rw [hcx]
    show dbl (neg x * u - v * conj (cdZero : CD m))
        (conj (neg x) * v + u * (cdZero : CD m))
      = dbl (neg (x * u)) (x * v)
    rw [conj_neg, hx, neg_neg, conj_zero, mul_zero, sub_zero, mul_zero, add_zero, neg_mul]
  have h2 : dbl y (cdZero : CD m) * dbl (neg (x * u)) (x * v)
      = dbl (neg (y * (x * u))) (neg (y * (x * v))) := by
    show dbl (y * neg (x * u) - (x * v) * conj (cdZero : CD m))
        (conj y * (x * v) + neg (x * u) * (cdZero : CD m))
      = dbl (neg (y * (x * u))) (neg (y * (x * v)))
    rw [hy, mul_neg, conj_zero, mul_zero, sub_zero, mul_zero, add_zero, neg_mul]
  have h3 : dbl y (cdZero : CD m) * dbl u v = dbl (y * u) (neg (y * v)) := by
    show dbl (y * u - v * conj (cdZero : CD m))
        (conj y * v + u * (cdZero : CD m))
      = dbl (y * u) (neg (y * v))
    rw [hy, conj_zero, mul_zero, sub_zero, mul_zero, add_zero, neg_mul]
  have h4 : conj (dbl x (cdZero : CD m)) * dbl (y * u) (neg (y * v))
      = dbl (neg (x * (y * u))) (neg (x * (y * v))) := by
    rw [hcx]
    show dbl (neg x * (y * u) - neg (y * v) * conj (cdZero : CD m))
        (conj (neg x) * neg (y * v) + (y * u) * (cdZero : CD m))
      = dbl (neg (x * (y * u))) (neg (x * (y * v)))
    rw [conj_neg, hx, neg_neg, conj_zero, mul_zero, sub_zero, mul_zero, add_zero,
      neg_mul, mul_neg]
  rw [h1, h3, h2, h4]
  show dbl (neg (y * (x * u)) + neg (x * (y * u)))
      (neg (y * (x * v)) + neg (x * (y * v)))
    = dbl (y * (conj x * u) + conj x * (y * u))
      (y * (conj x * v) + conj x * (y * v))
  rw [← neg_add, ← neg_add,
    ← C_eq_neg_anticommutator x y u hx, ← C_eq_neg_anticommutator x y v hx]

/-- If C vanishes for (x, y), it vanishes for the pair embedded one level up. -/
theorem C_zero_embed {m : ℕ} (x y : CD m) (hx : conj x = neg x) (hy : conj y = neg y)
    (hC : ∀ u : CD m, y * (conj x * u) + conj x * (y * u) = (cdZero : CD m))
    (w : CD (m + 1)) :
    dbl y (cdZero : CD m) * (conj (dbl x (cdZero : CD m)) * w)
      + conj (dbl x (cdZero : CD m)) * (dbl y (cdZero : CD m) * w)
      = (cdZero : CD (m + 1)) := by
  cases w with
  | dbl u v =>
    rw [C_embed x y u v hx hy, hC u, hC v]
    rfl

/-- **C ≡ 0 for the centre pair at every level.** At the quaternions the
full art is available, so C vanishes identically; each lower embedding
preserves that vanishing. -/
theorem C_zero_centre (k : ℕ) (w : CD (2 + k)) :
    embedN k unitJ * (conj (embedN k unitI) * w)
      + conj (embedN k unitI) * (embedN k unitJ * w)
      = (cdZero : CD (2 + k)) := by
  induction k with
  | zero =>
    exact C_eq_zero unitI unitJ conj_unitI unitI_sq hxy_units art_left_two w
  | succ n ih =>
    cases w with
    | dbl u v =>
      have hx : conj (embedN n unitI) = neg (embedN n unitI) := (centre_hyp n).1
      have hy : conj (embedN n unitJ) = neg (embedN n unitJ) := (centre_hyp n).2.2.1
      unfold embedN embed1
      rw [C_embed (embedN n unitI) (embedN n unitJ) u v hx hy, ih u, ih v]
      rfl

/-- Kernel form of the fold once C vanishes: the second block is free. -/
theorem ker_W_of_C_zero {m : ℕ} (x y a₀ a₁ : CD m)
    (hC : ∀ u : CD m, y * (conj x * u) + conj x * (y * u) = (cdZero : CD m)) :
    (dbl x (cdZero : CD m) * dbl a₀ a₁) * dbl y (cdZero : CD m)
      + dbl x (cdZero : CD m) * (dbl a₀ a₁ * dbl y (cdZero : CD m))
      = (cdZero : CD (m + 1)) ↔
    (x * a₀) * y + x * (a₀ * y) = (cdZero : CD m) := by
  rw [ker_WT_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hC a₁⟩⟩

theorem ker_WTP_of_C_zero {m : ℕ} (x y : CD m)
    (hC : ∀ u : CD m, y * (conj x * u) + conj x * (y * u) = (cdZero : CD m)) :
    LinearMap.ker (WTP x y)
      = LinearMap.ker ((WA x y).comp (LinearMap.fst ℝ (CD m) (CD m))) := by
  ext p
  constructor
  · intro h
    exact LinearMap.mem_ker.mpr
      ((ker_W_of_C_zero x y p.1 p.2 hC).mp (LinearMap.mem_ker.mp h))
  · intro h
    exact LinearMap.mem_ker.mpr
      ((ker_W_of_C_zero x y p.1 p.2 hC).mpr (LinearMap.mem_ker.mp h))

/-- Numeric fold once C vanishes: dim ker W_{m+1} = dim ker W_m + 2^m. -/
theorem finrank_ker_of_C_zero {m : ℕ} (x y : CD m)
    (hC : ∀ u : CD m, y * (conj x * u) + conj x * (y * u) = (cdZero : CD m)) :
    Module.finrank ℝ (LinearMap.ker (WT x y))
      = Module.finrank ℝ (LinearMap.ker (WA x y)) + 2 ^ m := by
  have h1 := ker_WTP_of_C_zero x y hC
  have h2 : LinearMap.range ((WA x y).comp (LinearMap.fst ℝ (CD m) (CD m)))
      = LinearMap.range (WA x y) := by
    ext v
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p.1, hp⟩
    · rintro ⟨a, ha⟩
      exact ⟨(a, (cdZero : CD m)), ha⟩
  have h3 := LinearMap.finrank_range_add_finrank_ker
    ((WA x y).comp (LinearMap.fst ℝ (CD m) (CD m)))
  have h4 := LinearMap.finrank_range_add_finrank_ker (WA x y)
  rw [h2, Module.finrank_prod, finrank_cd] at h3
  rw [finrank_cd] at h4
  have h5 : LinearMap.range (WTP x y) = LinearMap.range (WT x y) := by
    ext v
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨cdPairLm p, hp⟩
    · rintro ⟨u, hu⟩
      obtain ⟨p, hp⟩ := cdPairLm_surjective u
      exact ⟨p, by
        have hg : WT x y (cdPairLm p) = v := by rw [hp]; exact hu
        exact hg⟩
  have h6 := LinearMap.finrank_range_add_finrank_ker (WTP x y)
  have h7 := LinearMap.finrank_range_add_finrank_ker (WT x y)
  rw [h5, Module.finrank_prod, finrank_cd] at h6
  rw [finrank_cd, pow_succ, Nat.mul_two] at h7
  rw [h1] at h6
  omega

/-- **The centre pair attains the maximum at every level.**
dim ker W(i, j) embedded k times equals 2^{2+k} − 4: 0 in ℍ, 4 in 𝕆,
12 in the sedenions, 28 at dimension 64, 60 at dimension 128, and so on.
The quaternion art starts the induction; the embedding lift carries C ≡ 0
past the death of alternativity. -/
theorem finrank_ker_centre (k : ℕ) :
    Module.finrank ℝ (LinearMap.ker (WA (embedN k unitI) (embedN k unitJ)))
      = 2 ^ (2 + k) - 4 := by
  induction k with
  | zero =>
    have hE := LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective (WA unitI unitJ) WA_quaternion_injective)
    have hR := LinearMap.finrank_range_add_finrank_ker (WA unitI unitJ)
    rw [← hE] at hR
    have hK : Module.finrank ℝ (LinearMap.ker (WA unitI unitJ)) = 0 := by omega
    change Module.finrank ℝ (LinearMap.ker (WA unitI unitJ)) = 2 ^ (2 + 0) - 4
    rw [hK]
    decide
  | succ n ih =>
    have hpow : 2 ^ (2 + n) - 4 + 2 ^ (2 + n) = 2 ^ (2 + (n + 1)) - 4 := by
      have hle : 4 ≤ 2 ^ (2 + n) := by
        have h4 : 4 ≤ 2 ^ 2 := by decide
        exact Nat.le_trans h4 (Nat.pow_le_pow_right (by decide) (Nat.le_add_right 2 n))
      rw [Nat.add_comm, ← Nat.add_sub_assoc hle, ← Nat.mul_two, ← pow_succ, ← Nat.add_assoc]
    change Module.finrank ℝ (LinearMap.ker
        (WA (embed1 (embedN n unitI)) (embed1 (embedN n unitJ))))
      = 2 ^ (2 + (n + 1)) - 4
    unfold embed1
    rw [WA_eq_WT_embed,
      finrank_ker_of_C_zero (embedN n unitI) (embedN n unitJ) (C_zero_centre n), ih, hpow]

/-!
### Step (5) for a general pair: W on the quaternion, unit art only

For an imaginary pair the anti-associator sends the quaternion basis to
twice itself up to sign, and `conj x` preserves its span. No full
alternativity: only the left art of x, the right art of y, the squares
x² = y² = −1 and the quaternion relation y(xy) = −((xy)y). This is the
computation half of the directness H ∩ x·ker W = 0; what remains is the
linear independence of {1, x, y, xy} and the weak inclusion.
-/

/-- `conj x` sends 1 to −x. -/
theorem xbar_stab_one {m : ℕ} (x : CD m) (hx : conj x = neg x) :
    conj x * (cdOne : CD m) = neg x := by
  rw [hx, neg_mul, mul_one]

/-- `conj x` sends x to 1. -/
theorem xbar_stab_x {m : ℕ} (x : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m)) :
    conj x * x = (cdOne : CD m) := by
  rw [hx, neg_mul, hx2, neg_neg]

/-- `conj x` sends y to −(xy). -/
theorem xbar_stab_y {m : ℕ} (x y : CD m) (hx : conj x = neg x) :
    conj x * y = neg (x * y) := by
  rw [hx, neg_mul]

/-- `conj x` sends xy back to y, by the left unit art of x. -/
theorem xbar_stab_xy {m : ℕ} (x y : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m))
    (hartLx : ∀ w : CD m, x * (x * w) = (x * x) * w) :
    conj x * (x * y) = y := by
  have eL : x * (x * y) = neg y := by rw [hartLx y, hx2, neg_mul, one_mul]
  rw [hx, neg_mul, eL, neg_neg]

/-- W(1) = 2xy: no art at all, just the unit laws. -/
theorem W_val_one {m : ℕ} (x y : CD m) :
    (x * (cdOne : CD m)) * y + x * ((cdOne : CD m) * y)
      = (x * y) + (x * y) := by
  rw [mul_one, one_mul]

/-- W(x) = −2y, by the left unit art of x alone. -/
theorem W_val_x {m : ℕ} (x y : CD m)
    (hx2 : x * x = neg (cdOne : CD m))
    (hartLx : ∀ w : CD m, x * (x * w) = (x * x) * w) :
    (x * x) * y + x * (x * y) = neg y + neg y := by
  have e : x * (x * y) = neg y := by rw [hartLx y, hx2, neg_mul, one_mul]
  rw [hx2, neg_mul, one_mul, e]

/-- W(y) = −2x, by the right unit art of y alone. -/
theorem W_val_y {m : ℕ} (x y : CD m)
    (hy2 : y * y = neg (cdOne : CD m))
    (hartRy : ∀ w : CD m, (w * y) * y = w * (y * y)) :
    (x * y) * y + x * (y * y) = neg x + neg x := by
  have e1 : x * (y * y) = neg x := by rw [hy2, mul_neg, mul_one]
  rw [hartRy x, e1]

/-- W(xy) = 2, by the two unit arts plus y(xy) = −((xy)y). -/
theorem W_val_xy {m : ℕ} (x y : CD m)
    (hx2 : x * x = neg (cdOne : CD m)) (hy2 : y * y = neg (cdOne : CD m))
    (hyxy : y * (x * y) = neg ((x * y) * y))
    (hartLx : ∀ w : CD m, x * (x * w) = (x * x) * w)
    (hartRy : ∀ w : CD m, (w * y) * y = w * (y * y)) :
    (x * (x * y)) * y + x * ((x * y) * y)
      = (cdOne : CD m) + (cdOne : CD m) := by
  have eL : x * (x * y) = neg y := by rw [hartLx y, hx2, neg_mul, one_mul]
  have e1 : x * (y * y) = neg x := by rw [hy2, mul_neg, mul_one]
  have eR : y * (x * y) = x := by rw [hyxy, hartRy x, e1, neg_neg]
  have h1 : (x * y) * y = neg (y * (x * y)) := by rw [hyxy, neg_neg]
  have eR' : (x * y) * y = neg x := by rw [h1, eR]
  rw [eL, eR', neg_mul, mul_neg, hy2, hx2, neg_neg]

/-!
### ker W is stable under the two units; the weak inclusion, reduced

`W_stable_Lx/Ry`: the kernel of the anti-associator is preserved by left
multiplication by x (right by y), with only the unit art of x (of y).
`C_of_W_of_S`: the weak inclusion x·ker W ⊆ ker C follows from W(a) = 0
plus the two symmetric-part vanishings S_y(a) = a·y + y·a = 0 and
S_y(x·a) = 0 — verified numerically (0 fails over 930 pairs, 15960 kernel
generators, `sy_check.cpp`, exact mod-p arithmetic). Those two S_y facts
are proved by the unit-basis expansion in `weak_inclusion` below (floor
5), so the weak inclusion is now closed in Lean, not just numerically.
-/

/-- ker W is stable under L_x, by the left unit art of x alone. -/
theorem W_stable_Lx {m : ℕ} (x y a : CD m)
    (hx2 : x * x = neg (cdOne : CD m))
    (hartLx : ∀ w : CD m, x * (x * w) = (x * x) * w)
    (hW : (x * a) * y + x * (a * y) = (cdZero : CD m)) :
    (x * (x * a)) * y + x * ((x * a) * y) = (cdZero : CD m) := by
  have e1 : x * (x * a) = neg a := by rw [hartLx a, hx2, neg_mul, one_mul]
  have eH : x * ((x * a) * y) = a * y := by
    have h := congrArg (fun z => x * z) hW
    rw [mul_add', hartLx (a * y), hx2, neg_mul, one_mul, mul_zero] at h
    have h2 : x * ((x * a) * y) - a * y = (cdZero : CD m) := by
      rw [sub_add]
      exact h
    exact sub_eq_zero h2
  rw [e1, eH, neg_mul, neg_add_self]

/-- ker W is stable under R_y, by the right unit art of y alone. -/
theorem W_stable_Ry {m : ℕ} (x y a : CD m)
    (hy2 : y * y = neg (cdOne : CD m))
    (hartRy : ∀ w : CD m, (w * y) * y = w * (y * y))
    (hW : (x * a) * y + x * (a * y) = (cdZero : CD m)) :
    (x * (a * y)) * y + x * ((a * y) * y) = (cdZero : CD m) := by
  have e1 : (a * y) * y = neg a := by rw [hartRy a, hy2, mul_neg, mul_one]
  have eH : (x * (a * y)) * y = x * a := by
    have h := congrArg (fun z => z * y) hW
    rw [add_mul', hartRy (x * a), hy2, mul_neg, mul_one, zero_mul] at h
    rw [add_comm (neg (x * a)) _] at h
    have h2 : (x * (a * y)) * y - x * a = (cdZero : CD m) := by
      rw [sub_add]
      exact h
    exact sub_eq_zero h2
  rw [eH, e1, mul_neg, add_neg_self]

/-- Weak inclusion, reduced to the symmetric parts. If W(a) = 0 and both
a and x·a are y-perp (a·y + y·a = 0), then C(x·a) = 0 — with only the
left unit art of x. -/
theorem C_of_W_of_S {m : ℕ} (x y a : CD m) (hx : conj x = neg x)
    (hx2 : x * x = neg (cdOne : CD m))
    (hartLx : ∀ w : CD m, x * (x * w) = (x * x) * w)
    (hW : (x * a) * y + x * (a * y) = (cdZero : CD m))
    (hS0 : a * y + y * a = (cdZero : CD m))
    (hS1 : (x * a) * y + y * (x * a) = (cdZero : CD m)) :
    y * (conj x * (x * a)) + conj x * (y * (x * a)) = (cdZero : CD m) := by
  have e0 : conj x * (x * a) = a := by
    rw [hx, neg_mul, hartLx a, hx2, neg_mul, one_mul, neg_neg]
  have eH : x * ((x * a) * y) = a * y := by
    have h := congrArg (fun z => x * z) hW
    rw [mul_add', hartLx (a * y), hx2, neg_mul, one_mul, mul_zero] at h
    have h2 : x * ((x * a) * y) - a * y = (cdZero : CD m) := by
      rw [sub_add]
      exact h
    exact sub_eq_zero h2
  have hS0r : y * a + a * y = (cdZero : CD m) := by
    rw [add_comm (y * a) (a * y)]
    exact hS0
  have hS1r : y * (x * a) + (x * a) * y = (cdZero : CD m) := by
    rw [add_comm (y * (x * a)) ((x * a) * y)]
    exact hS1
  have eS0 : y * a = neg (a * y) := eq_neg_of_add_eq_zero_left hS0r
  have eS1 : y * (x * a) = neg ((x * a) * y) := eq_neg_of_add_eq_zero_left hS1r
  have hWant : x * (y * (x * a)) = y * a := by
    rw [eS1, mul_neg, eH, ← eS0]
  rw [e0, hx, neg_mul, hWant, add_neg_self]

/-!
### Floor 5, step C2: the weak inclusion, closed

`weak_inclusion`: for two DISTINCT imaginary units x, y, if x·a lies in
the kernel of the anti-associator W(u) = (x·u)·y + x·(u·y), then x·a
lies in the kernel of C(u) = y·(x̄·u) + x̄·(y·u). The two symmetric parts
that `C_of_W_of_S` leaves open are now supplied: expand a against the
basis of units; the four distinguished coefficients of {1, x, y, w = x·y}
die by reading W through the coordinates — W sends 1 ↦ 2w, x ↦ −2y,
y ↦ −2x, and w ↦ ±2, so the diagonal system is ±2·(coefficient) = 0 —
and on the fresh complement both S-parts vanish term by term, by the
anticommutator gate plus the ±-stability of x·(fresh) and (fresh)·y.
This closes the last Lean gap of the T12 chain: the weak inclusion now
holds for every pair of distinct imaginary units at every level.
-/

theorem weak_inclusion {m : ℕ} (x y a : CD m)
    (hbx : BasisUnit x) (hcx : conj x = neg x)
    (hby : BasisUnit y) (hcy : conj y = neg y) (hne : x ≠ y)
    (hW : (x * a) * y + x * (a * y) = (cdZero : CD m)) :
    y * (conj x * (x * a)) + conj x * (y * (x * a)) = (cdZero : CD m) := by
  -- Unit arts and square laws (a unit is either 1 or imaginary-square-−1).
  obtain ⟨hpx, hartLx, -⟩ := basisUnit_pack hbx
  rcases hpx with hreal | ⟨-, hx2⟩
  · rw [hreal] at hcx
    rw [conj_one] at hcx
    exact absurd hcx cdOne_ne_neg_one
  obtain ⟨hpy, -, hartRy⟩ := basisUnit_pack hby
  rcases hpy with hreal | ⟨-, hy2⟩
  · rw [hreal] at hcy
    rw [conj_one] at hcy
    exact absurd hcy cdOne_ne_neg_one
  -- The product unit w = ±x·y and the sign-splitting identities.
  obtain ⟨w, hbw, hcw, hwne_x, hwne_y, hxyw⟩ :=
    basisUnit_mul_distinct hbx hby hcx hcy hne
  have hyxy : y * (x * y) = neg ((x * y) * y) := by
    rcases hxyw with hc | hc
    · rw [hc]
      exact basisUnit_anticomm hbw hby hcw hcy hwne_y
    · rw [hc, mul_neg, neg_mul, neg_neg,
        basisUnit_anticomm hbw hby hcw hcy hwne_y, neg_neg]
  have hwxy_neg : x * y = neg w → w = neg (x * y) := by
    intro hc
    have h2 := congrArg neg hc
    rw [neg_neg] at h2
    exact h2.symm
  -- Indices for 1, x, y, w in the unit basis.
  obtain ⟨e1, he1⟩ := basisUnit_beval (basisUnit_cdOne m)
  obtain ⟨ex, hex⟩ := basisUnit_beval hbx
  obtain ⟨ey, hey⟩ := basisUnit_beval hby
  obtain ⟨ew, hew⟩ := basisUnit_beval hbw
  -- Index distinctness.
  have hCD1 : ∀ z : CD m, conj z = neg z → z ≠ (cdOne : CD m) := by
    intro z hz hz1
    rw [hz1] at hz
    rw [conj_one] at hz
    exact cdOne_ne_neg_one hz
  have hdv : ∀ p q : CD m, conj p = neg p → conj q = neg q → p ≠ q →
      ∀ u v : BUnit m, beval u = p → beval v = q → u ≠ v := by
    intro p q hp hq hpq u v hu hv h
    apply hpq
    rw [← hu, ← hv, h]
  have he1x : e1 ≠ ex := fun h => hCD1 x hcx (by rw [← hex, ← he1, h])
  have he1y : e1 ≠ ey := fun h => hCD1 y hcy (by rw [← hey, ← he1, h])
  have he1w : e1 ≠ ew := fun h => hCD1 w hcw (by rw [← hew, ← he1, h])
  have hexy : ex ≠ ey := hdv x y hcx hcy hne ex ey hex hey
  have hexw : ex ≠ ew := hdv x w hcx hcw (Ne.symm hwne_x) ex ew hex hew
  have heyw : ey ≠ ew := hdv y w hcy hcw (Ne.symm hwne_y) ey ew hey hew
  have hd1 : e1 ∉ ({ex, ey, ew} : Finset (BUnit m)) := by
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact he1x h'
    · rcases Finset.mem_insert.mp h' with h' | h'
      · exact he1y h'
      · exact he1w (Finset.mem_singleton.mp h')
  have hd2 : ex ∉ ({ey, ew} : Finset (BUnit m)) := by
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact hexy h'
    · exact hexw (Finset.mem_singleton.mp h')
  have hd3 : ey ∉ ({ew} : Finset (BUnit m)) :=
    fun h => heyw (Finset.mem_singleton.mp h)
  -- Freshness gates, reusable across the four coordinate readings.
  have hjor : ∀ j : BUnit m, j ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) →
      j = e1 ∨ j = ex ∨ j = ey ∨ j = ew := by
    intro j hj
    rcases Finset.mem_insert.mp hj with h | h
    · exact Or.inl h
    · rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr (Or.inl h)
      · rcases Finset.mem_insert.mp h with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp h)))
  have hmem : ∀ j : BUnit m, j = e1 ∨ j = ex ∨ j = ey ∨ j = ew →
      j ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) := by
    intro j hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp
  have hgate : ∀ i : BUnit m, i ∉ ({e1, ex, ey, ew} : Finset (BUnit m)) →
      i ≠ e1 ∧ i ≠ ex ∧ i ≠ ey ∧ i ≠ ew := by
    intro i hi
    exact ⟨fun h => hi (hmem i (Or.inl h)),
      fun h => hi (hmem i (Or.inr (Or.inl h))),
      fun h => hi (hmem i (Or.inr (Or.inr (Or.inl h)))),
      fun h => hi (hmem i (Or.inr (Or.inr (Or.inr h))))⟩
  have hfresh : ∀ (i : BUnit m),
      i ∈ Finset.univ \ ({e1, ex, ey, ew} : Finset (BUnit m)) →
      ∀ j : BUnit m, j ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) →
      coordLm j ((WA x y) (beval i)) = 0 := by
    intro i hi j hj
    obtain ⟨hi1, hix, hiy, hiw⟩ := hgate i (Finset.mem_sdiff.mp hi).2
    exact fresh_W_coord_zero x y w e1 ex ey ew hbx hcx hby hcy hbw hne hxyw
      he1 hex hey hew i hi1 hix hiy hiw j (hjor j hj)
  have hjew : ew ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) :=
    hmem ew (Or.inr (Or.inr (Or.inr rfl)))
  have hjey : ey ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) :=
    hmem ey (Or.inr (Or.inr (Or.inl rfl)))
  have hjex : ex ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) :=
    hmem ex (Or.inr (Or.inl rfl))
  have hje1 : e1 ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) :=
    hmem e1 (Or.inl rfl)
  -- W on the distinguished vectors, and the auxiliary sign-negations.
  have hW1 : (WA x y) ((cdOne : CD m)) = x * y + x * y := W_val_one x y
  have hWx : (WA x y) x = neg y + neg y := W_val_x x y hx2 hartLx
  have hWy : (WA x y) y = neg x + neg x := W_val_y x y hy2 hartRy
  have hWxy : (WA x y) (x * y) = cdOne + cdOne :=
    W_val_xy x y hx2 hy2 hyxy hartLx hartRy
  have hWneg : ∀ t : CD m, (WA x y) (neg t) = neg ((WA x y) t) :=
    fun t => map_neg (WA x y) t
  have hna : ∀ p q : CD m, neg p + neg q = neg (p + q) :=
    fun p q => (_root_.neg_add p q).symm
  -- Coordinate basics.
  have hce1 : coordLm e1 (beval e1) = 1 := by rw [coord_apply]; exact if_pos rfl
  have hcex : coordLm ex (beval ex) = 1 := by rw [coord_apply]; exact if_pos rfl
  have hcey : coordLm ey (beval ey) = 1 := by rw [coord_apply]; exact if_pos rfl
  have hcew : coordLm ew (beval ew) = 1 := by rw [coord_apply]; exact if_pos rfl
  -- Reading 1 (j = ew): kills the 1-coordinate of a.
  have hWa : (WA x y) a = (cdZero : CD m) := hW
  have h0ew : coordLm ew ((WA x y) a) = 0 := by
    rw [hWa]
    exact map_zero (coordLm ew)
  rw [W_coord_split x y e1 ex ey ew a hd1 hd2 hd3 ew
      (fun i hi => hfresh i hi ew hjew)] at h0ew
  obtain ⟨sew, hsew, pew1⟩ : ∃ s : ℝ, s ≠ 0 ∧
      coordLm ew ((WA x y) (beval e1)) = s := by
    rcases hxyw with hc | hc
    · refine ⟨2, by norm_num, ?_⟩
      rw [he1, hW1, map_add, hc, ← hew, hcew]
      norm_num
    · refine ⟨-2, by norm_num, ?_⟩
      rw [he1, hW1, map_add, hc, coord_neg, ← hew, hcew]
      norm_num
  have pewx : coordLm ew ((WA x y) (beval ex)) = 0 := by
    rw [hex, hWx, map_add, coord_neg, ← hey, coord_val_ne ey ew heyw]
    norm_num
  have pewy : coordLm ew ((WA x y) (beval ey)) = 0 := by
    rw [hey, hWy, map_add, coord_neg, ← hex, coord_val_ne ex ew hexw]
    norm_num
  have peww : coordLm ew ((WA x y) (beval ew)) = 0 := by
    rcases hxyw with hc | hc
    · rw [hew, ← hc, hWxy, ← he1, map_add, coord_val_ne e1 ew he1w]
      norm_num
    · rw [hew, hwxy_neg hc, hWneg, hWxy, coord_neg, ← he1, map_add,
        coord_val_ne e1 ew he1w]
      norm_num
  rw [pew1, pewx, pewy, peww] at h0ew
  simp only [MulZeroClass.mul_zero, AddZeroClass.add_zero] at h0ew
  have ce1z : (bevalBasis m).repr a e1 = 0 :=
    (mul_eq_zero.mp h0ew).resolve_right hsew
  -- Reading 2 (j = ey): kills the x-coordinate of a.
  have h0ey : coordLm ey ((WA x y) a) = 0 := by
    rw [hWa]
    exact map_zero (coordLm ey)
  rw [W_coord_split x y e1 ex ey ew a hd1 hd2 hd3 ey
      (fun i hi => hfresh i hi ey hjey)] at h0ey
  have pey1 : coordLm ey ((WA x y) (beval e1)) = 0 := by
    rw [he1, hW1, map_add]
    rcases hxyw with hc | hc
    · rw [hc, ← hew, coord_val_ne ew ey (Ne.symm heyw)]
      norm_num
    · rw [hc, coord_neg, ← hew, coord_val_ne ew ey (Ne.symm heyw)]
      norm_num
  have peyx : coordLm ey ((WA x y) (beval ex)) = -2 := by
    rw [hex, hWx, map_add, coord_neg, ← hey, hcey]
    norm_num
  have peyy : coordLm ey ((WA x y) (beval ey)) = 0 := by
    rw [hey, hWy, map_add, coord_neg, ← hex, coord_val_ne ex ey hexy]
    norm_num
  have peyw : coordLm ey ((WA x y) (beval ew)) = 0 := by
    rcases hxyw with hc | hc
    · rw [hew, ← hc, hWxy, ← he1, map_add, coord_val_ne e1 ey he1y]
      norm_num
    · rw [hew, hwxy_neg hc, hWneg, hWxy, coord_neg, ← he1, map_add,
        coord_val_ne e1 ey he1y]
      norm_num
  rw [pey1, peyx, peyy, peyw] at h0ey
  simp only [MulZeroClass.mul_zero, AddZeroClass.add_zero, AddZeroClass.zero_add] at h0ey
  have cexz : (bevalBasis m).repr a ex = 0 :=
    (mul_eq_zero.mp h0ey).resolve_right (by norm_num)
  -- Reading 3 (j = ex): kills the y-coordinate of a.
  have h0ex : coordLm ex ((WA x y) a) = 0 := by
    rw [hWa]
    exact map_zero (coordLm ex)
  rw [W_coord_split x y e1 ex ey ew a hd1 hd2 hd3 ex
      (fun i hi => hfresh i hi ex hjex)] at h0ex
  have pex1 : coordLm ex ((WA x y) (beval e1)) = 0 := by
    rw [he1, hW1, map_add]
    rcases hxyw with hc | hc
    · rw [hc, ← hew, coord_val_ne ew ex (Ne.symm hexw)]
      norm_num
    · rw [hc, coord_neg, ← hew, coord_val_ne ew ex (Ne.symm hexw)]
      norm_num
  have pexx : coordLm ex ((WA x y) (beval ex)) = 0 := by
    rw [hex, hWx, map_add, coord_neg, ← hey, coord_val_ne ey ex (Ne.symm hexy)]
    norm_num
  have pexy : coordLm ex ((WA x y) (beval ey)) = -2 := by
    rw [hey, hWy, map_add, coord_neg, ← hex, hcex]
    norm_num
  have pexw : coordLm ex ((WA x y) (beval ew)) = 0 := by
    rcases hxyw with hc | hc
    · rw [hew, ← hc, hWxy, ← he1, map_add, coord_val_ne e1 ex he1x]
      norm_num
    · rw [hew, hwxy_neg hc, hWneg, hWxy, coord_neg, ← he1, map_add,
        coord_val_ne e1 ex he1x]
      norm_num
  rw [pex1, pexx, pexy, pexw] at h0ex
  simp only [MulZeroClass.mul_zero, AddZeroClass.add_zero, AddZeroClass.zero_add] at h0ex
  have ceyz : (bevalBasis m).repr a ey = 0 :=
    (mul_eq_zero.mp h0ex).resolve_right (by norm_num)
  -- Reading 4 (j = e1): kills the w-coordinate of a.
  have h0e1 : coordLm e1 ((WA x y) a) = 0 := by
    rw [hWa]
    exact map_zero (coordLm e1)
  rw [W_coord_split x y e1 ex ey ew a hd1 hd2 hd3 e1
      (fun i hi => hfresh i hi e1 hje1)] at h0e1
  have pe11 : coordLm e1 ((WA x y) (beval e1)) = 0 := by
    rw [he1, hW1, map_add]
    rcases hxyw with hc | hc
    · rw [hc, ← hew, coord_val_ne ew e1 (Ne.symm he1w)]
      norm_num
    · rw [hc, coord_neg, ← hew, coord_val_ne ew e1 (Ne.symm he1w)]
      norm_num
  have pe1x : coordLm e1 ((WA x y) (beval ex)) = 0 := by
    rw [hex, hWx, map_add, coord_neg, ← hey, coord_val_ne ey e1 (Ne.symm he1y)]
    norm_num
  have pe1y : coordLm e1 ((WA x y) (beval ey)) = 0 := by
    rw [hey, hWy, map_add, coord_neg, ← hex, coord_val_ne ex e1 (Ne.symm he1x)]
    norm_num
  obtain ⟨se1, hse1, pe1w⟩ : ∃ s : ℝ, s ≠ 0 ∧
      coordLm e1 ((WA x y) (beval ew)) = s := by
    rcases hxyw with hc | hc
    · refine ⟨2, by norm_num, ?_⟩
      rw [hew, ← hc, hWxy, ← he1, map_add, hce1]
      norm_num
    · refine ⟨-2, by norm_num, ?_⟩
      rw [hew, hwxy_neg hc, hWneg, hWxy, coord_neg, ← he1, map_add, hce1]
      norm_num
  rw [pe11, pe1x, pe1y, pe1w] at h0e1
  simp only [MulZeroClass.mul_zero, AddZeroClass.add_zero, AddZeroClass.zero_add] at h0e1
  have cewz : (bevalBasis m).repr a ew = 0 :=
    (mul_eq_zero.mp h0e1).resolve_right hse1
  -- a has no distinguished component; a lives in the fresh complement.
  have hH0 : ∑ i ∈ ({e1, ex, ey, ew} : Finset (BUnit m)),
      (bevalBasis m).repr a i • beval i = (cdZero : CD m) := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rcases Finset.mem_insert.mp hi with h | h
    · rw [h, ce1z, _root_.zero_smul]
    · rcases Finset.mem_insert.mp h with h | h
      · rw [h, cexz, _root_.zero_smul]
      · rcases Finset.mem_insert.mp h with h | h
        · rw [h, ceyz, _root_.zero_smul]
        · rw [Finset.mem_singleton.mp h, cewz, _root_.zero_smul]
  have ha' : a = ∑ i ∈ (Finset.univ \ ({e1, ex, ey, ew} : Finset (BUnit m))),
      (bevalBasis m).repr a i • beval i := by
    conv_lhs => rw [a_decomp e1 ex ey ew a]
    rw [hH0, zero_add]
  -- S_y(a) = 0: fresh units are y-perp by the anticommutator.
  have hS0 : a * y + y * a = (cdZero : CD m) := by
    rw [ha', cd_sum_mul_left _ _ y, cd_sum_mul_right _ y,
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    obtain ⟨hi1, hix, hiy, hiw⟩ := hgate i (Finset.mem_sdiff.mp hi).2
    rw [smul_mul_left', smul_mul_right', ← smul_add'',
      fresh_anticomm y e1 ey hby hcy he1 hey i hi1 hiy]
    exact smul_zero' _
  -- S_y(x·a) = 0: x sends fresh indices to fresh units (±), and each
  -- fresh unit is y-perp.
  have hS1 : (x * a) * y + y * (x * a) = (cdZero : CD m) := by
    rw [ha', cd_sum_mul_right _ x, cd_sum_mul_right _ y,
      cd_sum_mul_left _ _ y, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    obtain ⟨hi1, hix, hiy, hiw⟩ := hgate i (Finset.mem_sdiff.mp hi).2
    obtain ⟨v, hv1, hvx, hvy, hvw, hs⟩ :=
      fresh_mul_left x y w e1 ex ey ew hbx hcx hby hcy hbw hne hxyw
        he1 hex hey hew i hi1 hix hiy hiw
    rcases hs with h | h
    · rw [smul_mul_right', smul_mul_left', smul_mul_right', ← smul_add'', h,
        fresh_anticomm y e1 ey hby hcy he1 hey v hv1 hvy]
      exact smul_zero' _
    · rw [smul_mul_right', smul_mul_left', smul_mul_right', ← smul_add'', h,
        neg_mul, mul_neg, hna,
        fresh_anticomm y e1 ey hby hcy he1 hey v hv1 hvy, neg_zero]
      exact smul_zero' _
  exact C_of_W_of_S x y a hcx hx2 hartLx hW hS0 hS1

/-!
### The fold law off full alternativity

A single imaginary basis unit is left-bijective at every level: the unit art
gives x·(x·t) = −t, so left multiplication by x and by −x are inverse linear
maps. The complementary block C is linear for the same reason W_A is. On the
fresh complement of H = span{1, x, y, xy} the two symmetric parts vanish
without any hypothesis on W, and the resulting operator identity is
C(x·f) = x·W(f). That is check F, and with the block lemma it is the fold.
-/

/-- Left multiplication by an imaginary basis unit is inverted by
multiplication by its negative. The art hypothesis is the unit art of x
alone. -/
theorem basisUnit_mulLeft_right_inv {m : ℕ} {x : CD m}
    (hx : BasisUnit x) (hcx : conj x = neg x) :
    (mulLeft x).comp (mulLeft (neg x)) = LinearMap.id := by
  ext a
  show x * (neg x * a) = a
  rw [neg_mul, mul_neg, basisUnit_left_art hx a, basisUnit_sq hx hcx,
    neg_one_mul, neg_neg]

theorem basisUnit_mulLeft_left_inv {m : ℕ} {x : CD m}
    (hx : BasisUnit x) (hcx : conj x = neg x) :
    (mulLeft (neg x)).comp (mulLeft x) = LinearMap.id := by
  ext a
  show neg x * (x * a) = a
  rw [neg_mul, basisUnit_left_art hx a, basisUnit_sq hx hcx, neg_one_mul, neg_neg]

/-- L_x as a linear automorphism, from the unit art. -/
noncomputable def basisUnit_Lx {m : ℕ} {x : CD m}
    (hx : BasisUnit x) (hcx : conj x = neg x) : CD m ≃ₗ[ℝ] CD m :=
  LinearEquiv.ofLinearMap (mulLeft x) (mulLeft (neg x))
    (basisUnit_mulLeft_right_inv hx hcx) (basisUnit_mulLeft_left_inv hx hcx)

/-- The complementary block C(u) = y·(x̄·u) + x̄·(y·u), as a linear map. -/
def CA {m : ℕ} (x y : CD m) : CD m →ₗ[ℝ] CD m :=
  (mulLeft y).comp (mulLeft (conj x)) + (mulLeft (conj x)).comp (mulLeft y)

theorem CA_apply {m : ℕ} (x y a : CD m) :
    CA x y a = y * (conj x * a) + conj x * (y * a) := rfl

/-- Equality in a four-element index set implies membership. -/
theorem quad_mem {m : ℕ} (e1 ex ey ew j : BUnit m)
    (hj : j = e1 ∨ j = ex ∨ j = ey ∨ j = ew) :
    j ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) := by
  rcases hj with rfl | rfl | rfl | rfl <;> simp

/-- An index outside the four-element set misses each of them. -/
theorem quad_gate {m : ℕ} (e1 ex ey ew i : BUnit m)
    (hi : i ∉ ({e1, ex, ey, ew} : Finset (BUnit m))) :
    i ≠ e1 ∧ i ≠ ex ∧ i ≠ ey ∧ i ≠ ew :=
  ⟨fun h => hi (quad_mem e1 ex ey ew i (Or.inl h)),
    fun h => hi (quad_mem e1 ex ey ew i (Or.inr (Or.inl h))),
    fun h => hi (quad_mem e1 ex ey ew i (Or.inr (Or.inr (Or.inl h)))),
    fun h => hi (quad_mem e1 ex ey ew i (Or.inr (Or.inr (Or.inr h))))⟩

/-- Membership in the four-element set is one of the four equalities. -/
theorem quad_jor {m : ℕ} (e1 ex ey ew j : BUnit m)
    (hj : j ∈ ({e1, ex, ey, ew} : Finset (BUnit m))) :
    j = e1 ∨ j = ex ∨ j = ey ∨ j = ew := by
  rcases Finset.mem_insert.mp hj with h | h
  · exact Or.inl h
  · rcases Finset.mem_insert.mp h with h | h
    · exact Or.inr (Or.inl h)
    · rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp h)))

/-- The coordinate functional reads the basis representation. -/
theorem coordLm_repr {m : ℕ} (j : BUnit m) (a : CD m) :
    coordLm j a = (bevalBasis m).repr a j := by
  simp [coordLm, Finsupp.lapply_apply]

/-- Projection onto the four distinguished coordinates. -/
noncomputable def Hpart {m : ℕ} (e1 ex ey ew : BUnit m) : CD m →ₗ[ℝ] CD m :=
  (coordLm e1).smulRight (beval e1)
    + ((coordLm ex).smulRight (beval ex)
        + ((coordLm ey).smulRight (beval ey)
            + (coordLm ew).smulRight (beval ew)))

theorem Hpart_apply {m : ℕ} (e1 ex ey ew : BUnit m) (a : CD m) :
    Hpart e1 ex ey ew a =
      coordLm e1 a • beval e1
        + (coordLm ex a • beval ex
            + (coordLm ey a • beval ey + coordLm ew a • beval ew)) := rfl

theorem Hset_sum_eq {m : ℕ} (e1 ex ey ew : BUnit m)
    (hd1 : e1 ∉ ({ex, ey, ew} : Finset (BUnit m)))
    (hd2 : ex ∉ ({ey, ew} : Finset (BUnit m)))
    (hd3 : ey ∉ ({ew} : Finset (BUnit m)))
    (g : BUnit m → CD m) :
    ∑ i ∈ ({e1, ex, ey, ew} : Finset (BUnit m)), g i
      = g e1 + (g ex + (g ey + g ew)) := by
  rw [Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_insert hd3,
    Finset.sum_singleton]

/-- A pair of distinct imaginary basis units, with the quaternion indices
{1, x, y, w = ±xy} already chosen and proved distinct. -/
structure ImagPair (m : ℕ) where
  x : CD m
  y : CD m
  bx : BasisUnit x
  cx : conj x = neg x
  byY : BasisUnit y
  cy : conj y = neg y
  ne : x ≠ y
  w : CD m
  bw : BasisUnit w
  cw : conj w = neg w
  wneX : w ≠ x
  wneY : w ≠ y
  xy : x * y = w ∨ x * y = neg w
  e1 : BUnit m
  ex : BUnit m
  ey : BUnit m
  ew : BUnit m
  he1 : beval e1 = (cdOne : CD m)
  hex : beval ex = x
  hey : beval ey = y
  hew : beval ew = w
  he1x : e1 ≠ ex
  he1y : e1 ≠ ey
  he1w : e1 ≠ ew
  hexy : ex ≠ ey
  hexw : ex ≠ ew
  heyw : ey ≠ ew
  hd1 : e1 ∉ ({ex, ey, ew} : Finset (BUnit m))
  hd2 : ex ∉ ({ey, ew} : Finset (BUnit m))
  hd3 : ey ∉ ({ew} : Finset (BUnit m))

theorem ImagPair.sqx {m : ℕ} (P : ImagPair m) :
    P.x * P.x = neg (cdOne : CD m) := basisUnit_sq P.bx P.cx

theorem ImagPair.sqy {m : ℕ} (P : ImagPair m) :
    P.y * P.y = neg (cdOne : CD m) := basisUnit_sq P.byY P.cy

theorem ImagPair.artLx {m : ℕ} (P : ImagPair m) (t : CD m) :
    P.x * (P.x * t) = (P.x * P.x) * t := basisUnit_left_art P.bx t

theorem ImagPair.artRy {m : ℕ} (P : ImagPair m) (t : CD m) :
    (t * P.y) * P.y = t * (P.y * P.y) := basisUnit_right_art P.byY t

noncomputable def ImagPair.Lx {m : ℕ} (P : ImagPair m) : CD m ≃ₗ[ℝ] CD m :=
  basisUnit_Lx P.bx P.cx

def ImagPair.Hset {m : ℕ} (P : ImagPair m) : Finset (BUnit m) :=
  {P.e1, P.ex, P.ey, P.ew}

theorem ImagPair.hyxy {m : ℕ} (P : ImagPair m) :
    P.y * (P.x * P.y) = neg ((P.x * P.y) * P.y) := by
  rcases P.xy with hc | hc
  · rw [hc]
    exact basisUnit_anticomm P.bw P.byY P.cw P.cy P.wneY
  · rw [hc, mul_neg, neg_mul, neg_neg,
      basisUnit_anticomm P.bw P.byY P.cw P.cy P.wneY, neg_neg]

theorem ImagPair.w_of_neg {m : ℕ} (P : ImagPair m) (hc : P.x * P.y = neg P.w) :
    P.w = neg (P.x * P.y) := by
  have h2 := congrArg neg hc
  rw [neg_neg] at h2
  exact h2.symm

/-- Every distinct imaginary basis pair carries such indices, and the
chosen pair is the one that was given. -/
theorem ImagPair.exists_eq {m : ℕ} (x y : CD m)
    (hbx : BasisUnit x) (hcx : conj x = neg x)
    (hby : BasisUnit y) (hcy : conj y = neg y) (hne : x ≠ y) :
    ∃ P : ImagPair m, P.x = x ∧ P.y = y := by
  obtain ⟨hpx, -, -⟩ := basisUnit_pack hbx
  rcases hpx with hreal | ⟨-, -⟩
  · rw [hreal] at hcx
    rw [conj_one] at hcx
    exact absurd hcx cdOne_ne_neg_one
  obtain ⟨hpy, -, -⟩ := basisUnit_pack hby
  rcases hpy with hreal | ⟨-, -⟩
  · rw [hreal] at hcy
    rw [conj_one] at hcy
    exact absurd hcy cdOne_ne_neg_one
  obtain ⟨w, hbw, hcw, hwne_x, hwne_y, hxyw⟩ :=
    basisUnit_mul_distinct hbx hby hcx hcy hne
  obtain ⟨e1, he1⟩ := basisUnit_beval (basisUnit_cdOne m)
  obtain ⟨ex, hex⟩ := basisUnit_beval hbx
  obtain ⟨ey, hey⟩ := basisUnit_beval hby
  obtain ⟨ew, hew⟩ := basisUnit_beval hbw
  have hCD1 : ∀ z : CD m, conj z = neg z → z ≠ (cdOne : CD m) := by
    intro z hz hz1
    rw [hz1] at hz
    rw [conj_one] at hz
    exact cdOne_ne_neg_one hz
  have hdv : ∀ p q : CD m, conj p = neg p → conj q = neg q → p ≠ q →
      ∀ u v : BUnit m, beval u = p → beval v = q → u ≠ v := by
    intro p q _ _ hpq u v hu hv h
    apply hpq
    rw [← hu, ← hv, h]
  have he1x : e1 ≠ ex := fun h => hCD1 x hcx (by rw [← hex, ← he1, h])
  have he1y : e1 ≠ ey := fun h => hCD1 y hcy (by rw [← hey, ← he1, h])
  have he1w : e1 ≠ ew := fun h => hCD1 w hcw (by rw [← hew, ← he1, h])
  have hexy : ex ≠ ey := hdv x y hcx hcy hne ex ey hex hey
  have hexw : ex ≠ ew := hdv x w hcx hcw (Ne.symm hwne_x) ex ew hex hew
  have heyw : ey ≠ ew := hdv y w hcy hcw (Ne.symm hwne_y) ey ew hey hew
  have hd1 : e1 ∉ ({ex, ey, ew} : Finset (BUnit m)) := by
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact he1x h'
    · rcases Finset.mem_insert.mp h' with h' | h'
      · exact he1y h'
      · exact he1w (Finset.mem_singleton.mp h')
  have hd2 : ex ∉ ({ey, ew} : Finset (BUnit m)) := by
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact hexy h'
    · exact hexw (Finset.mem_singleton.mp h')
  have hd3 : ey ∉ ({ew} : Finset (BUnit m)) :=
    fun h => heyw (Finset.mem_singleton.mp h)
  exact ⟨⟨x, y, hbx, hcx, hby, hcy, hne, w, hbw, hcw, hwne_x, hwne_y, hxyw,
    e1, ex, ey, ew, he1, hex, hey, hew, he1x, he1y, he1w, hexy, hexw, heyw,
    hd1, hd2, hd3⟩, rfl, rfl⟩

theorem ImagPair.Hsum_eq_Hpart {m : ℕ} (P : ImagPair m) (a : CD m) :
    ∑ i ∈ P.Hset, (bevalBasis m).repr a i • beval i
      = Hpart P.e1 P.ex P.ey P.ew a := by
  rw [show P.Hset = ({P.e1, P.ex, P.ey, P.ew} : Finset (BUnit m)) from rfl,
    Hset_sum_eq P.e1 P.ex P.ey P.ew P.hd1 P.hd2 P.hd3,
    Hpart_apply]
  simp only [coordLm_repr]

/-- Vanishing of the H-projection means the vector is its fresh sum. -/
theorem ImagPair.eq_fresh_sum {m : ℕ} (P : ImagPair m) (a : CD m)
    (hH : Hpart P.e1 P.ex P.ey P.ew a = (cdZero : CD m)) :
    a = ∑ i ∈ Finset.univ \ ({P.e1, P.ex, P.ey, P.ew} : Finset (BUnit m)),
      (bevalBasis m).repr a i • beval i := by
  conv_lhs => rw [a_decomp P.e1 P.ex P.ey P.ew a]
  have hsum := P.Hsum_eq_Hpart a
  rw [show P.Hset = ({P.e1, P.ex, P.ey, P.ew} : Finset (BUnit m)) from rfl] at hsum
  rw [hsum, hH, zero_add]

/-- W(a) = 0 kills the four H-coordinates. The ±2 table is the same
reading as `weak_inclusion`; it is restated so the kernel inclusion
`ker W ⊆ H^⊥` is a named lemma. -/
theorem ImagPair.ker_Hcoords {m : ℕ} (P : ImagPair m) (a : CD m)
    (hW : (WA P.x P.y) a = (cdZero : CD m)) :
    (bevalBasis m).repr a P.e1 = 0 ∧ (bevalBasis m).repr a P.ex = 0 ∧
      (bevalBasis m).repr a P.ey = 0 ∧ (bevalBasis m).repr a P.ew = 0 := by
  rcases P with ⟨x, y, hbx, hcx, hby, hcy, hne, w, hbw, hcw, hwne_x, hwne_y, hxyw,
    e1, ex, ey, ew, he1, hex, hey, hew, he1x, he1y, he1w, hexy, hexw, heyw,
    hd1, hd2, hd3⟩
  have hx2 : x * x = neg (cdOne : CD m) := basisUnit_sq hbx hcx
  have hy2 : y * y = neg (cdOne : CD m) := basisUnit_sq hby hcy
  have hartLx : ∀ t : CD m, x * (x * t) = (x * x) * t := basisUnit_left_art hbx
  have hartRy : ∀ t : CD m, (t * y) * y = t * (y * y) := basisUnit_right_art hby
  have hyxy : y * (x * y) = neg ((x * y) * y) := by
    rcases hxyw with hc | hc
    · rw [hc]
      exact basisUnit_anticomm hbw hby hcw hcy hwne_y
    · rw [hc, mul_neg, neg_mul, neg_neg,
        basisUnit_anticomm hbw hby hcw hcy hwne_y, neg_neg]
  have hwxy_neg : x * y = neg w → w = neg (x * y) := by
    intro hc
    have h2 := congrArg neg hc
    rw [neg_neg] at h2
    exact h2.symm
  have hfresh : ∀ (i : BUnit m),
      i ∈ Finset.univ \ ({e1, ex, ey, ew} : Finset (BUnit m)) →
      ∀ j : BUnit m, j ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) →
      coordLm j ((WA x y) (beval i)) = 0 := by
    intro i hi j hj
    obtain ⟨hi1, hix, hiy, hiw⟩ := quad_gate e1 ex ey ew i (Finset.mem_sdiff.mp hi).2
    exact fresh_W_coord_zero x y w e1 ex ey ew hbx hcx hby hcy hbw hne hxyw
      he1 hex hey hew i hi1 hix hiy hiw j (quad_jor e1 ex ey ew j hj)
  have hjew : ew ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) :=
    quad_mem e1 ex ey ew ew (Or.inr (Or.inr (Or.inr rfl)))
  have hjey : ey ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) :=
    quad_mem e1 ex ey ew ey (Or.inr (Or.inr (Or.inl rfl)))
  have hjex : ex ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) :=
    quad_mem e1 ex ey ew ex (Or.inr (Or.inl rfl))
  have hje1 : e1 ∈ ({e1, ex, ey, ew} : Finset (BUnit m)) :=
    quad_mem e1 ex ey ew e1 (Or.inl rfl)
  have hW1 : (WA x y) ((cdOne : CD m)) = x * y + x * y := W_val_one x y
  have hWx : (WA x y) x = neg y + neg y := W_val_x x y hx2 hartLx
  have hWy : (WA x y) y = neg x + neg x := W_val_y x y hy2 hartRy
  have hWxy : (WA x y) (x * y) = cdOne + cdOne :=
    W_val_xy x y hx2 hy2 hyxy hartLx hartRy
  have hWneg : ∀ t : CD m, (WA x y) (neg t) = neg ((WA x y) t) :=
    fun t => map_neg (WA x y) t
  have hce1 : coordLm e1 (beval e1) = 1 := by rw [coord_apply]; exact if_pos rfl
  have hcex : coordLm ex (beval ex) = 1 := by rw [coord_apply]; exact if_pos rfl
  have hcey : coordLm ey (beval ey) = 1 := by rw [coord_apply]; exact if_pos rfl
  have hcew : coordLm ew (beval ew) = 1 := by rw [coord_apply]; exact if_pos rfl
  have hWa : (WA x y) a = (cdZero : CD m) := hW
  have h0ew : coordLm ew ((WA x y) a) = 0 := by
    rw [hWa]
    exact map_zero (coordLm ew)
  rw [W_coord_split x y e1 ex ey ew a hd1 hd2 hd3 ew
      (fun i hi => hfresh i hi ew hjew)] at h0ew
  obtain ⟨sew, hsew, pew1⟩ : ∃ s : ℝ, s ≠ 0 ∧
      coordLm ew ((WA x y) (beval e1)) = s := by
    rcases hxyw with hc | hc
    · refine ⟨2, by norm_num, ?_⟩
      rw [he1, hW1, map_add, hc, ← hew, hcew]
      norm_num
    · refine ⟨-2, by norm_num, ?_⟩
      rw [he1, hW1, map_add, hc, coord_neg, ← hew, hcew]
      norm_num
  have pewx : coordLm ew ((WA x y) (beval ex)) = 0 := by
    rw [hex, hWx, map_add, coord_neg, ← hey, coord_val_ne ey ew heyw]
    norm_num
  have pewy : coordLm ew ((WA x y) (beval ey)) = 0 := by
    rw [hey, hWy, map_add, coord_neg, ← hex, coord_val_ne ex ew hexw]
    norm_num
  have peww : coordLm ew ((WA x y) (beval ew)) = 0 := by
    rcases hxyw with hc | hc
    · rw [hew, ← hc, hWxy, ← he1, map_add, coord_val_ne e1 ew he1w]
      norm_num
    · rw [hew, hwxy_neg hc, hWneg, hWxy, coord_neg, ← he1, map_add,
        coord_val_ne e1 ew he1w]
      norm_num
  rw [pew1, pewx, pewy, peww] at h0ew
  simp only [MulZeroClass.mul_zero, AddZeroClass.add_zero] at h0ew
  have ce1z : (bevalBasis m).repr a e1 = 0 :=
    (mul_eq_zero.mp h0ew).resolve_right hsew
  have h0ey : coordLm ey ((WA x y) a) = 0 := by
    rw [hWa]
    exact map_zero (coordLm ey)
  rw [W_coord_split x y e1 ex ey ew a hd1 hd2 hd3 ey
      (fun i hi => hfresh i hi ey hjey)] at h0ey
  have pey1 : coordLm ey ((WA x y) (beval e1)) = 0 := by
    rw [he1, hW1, map_add]
    rcases hxyw with hc | hc
    · rw [hc, ← hew, coord_val_ne ew ey (Ne.symm heyw)]
      norm_num
    · rw [hc, coord_neg, ← hew, coord_val_ne ew ey (Ne.symm heyw)]
      norm_num
  have peyx : coordLm ey ((WA x y) (beval ex)) = -2 := by
    rw [hex, hWx, map_add, coord_neg, ← hey, hcey]
    norm_num
  have peyy : coordLm ey ((WA x y) (beval ey)) = 0 := by
    rw [hey, hWy, map_add, coord_neg, ← hex, coord_val_ne ex ey hexy]
    norm_num
  have peyw : coordLm ey ((WA x y) (beval ew)) = 0 := by
    rcases hxyw with hc | hc
    · rw [hew, ← hc, hWxy, ← he1, map_add, coord_val_ne e1 ey he1y]
      norm_num
    · rw [hew, hwxy_neg hc, hWneg, hWxy, coord_neg, ← he1, map_add,
        coord_val_ne e1 ey he1y]
      norm_num
  rw [pey1, peyx, peyy, peyw] at h0ey
  simp only [MulZeroClass.mul_zero, AddZeroClass.add_zero, AddZeroClass.zero_add] at h0ey
  have cexz : (bevalBasis m).repr a ex = 0 :=
    (mul_eq_zero.mp h0ey).resolve_right (by norm_num)
  have h0ex : coordLm ex ((WA x y) a) = 0 := by
    rw [hWa]
    exact map_zero (coordLm ex)
  rw [W_coord_split x y e1 ex ey ew a hd1 hd2 hd3 ex
      (fun i hi => hfresh i hi ex hjex)] at h0ex
  have pex1 : coordLm ex ((WA x y) (beval e1)) = 0 := by
    rw [he1, hW1, map_add]
    rcases hxyw with hc | hc
    · rw [hc, ← hew, coord_val_ne ew ex (Ne.symm hexw)]
      norm_num
    · rw [hc, coord_neg, ← hew, coord_val_ne ew ex (Ne.symm hexw)]
      norm_num
  have pexx : coordLm ex ((WA x y) (beval ex)) = 0 := by
    rw [hex, hWx, map_add, coord_neg, ← hey, coord_val_ne ey ex (Ne.symm hexy)]
    norm_num
  have pexy : coordLm ex ((WA x y) (beval ey)) = -2 := by
    rw [hey, hWy, map_add, coord_neg, ← hex, hcex]
    norm_num
  have pexw : coordLm ex ((WA x y) (beval ew)) = 0 := by
    rcases hxyw with hc | hc
    · rw [hew, ← hc, hWxy, ← he1, map_add, coord_val_ne e1 ex he1x]
      norm_num
    · rw [hew, hwxy_neg hc, hWneg, hWxy, coord_neg, ← he1, map_add,
        coord_val_ne e1 ex he1x]
      norm_num
  rw [pex1, pexx, pexy, pexw] at h0ex
  simp only [MulZeroClass.mul_zero, AddZeroClass.add_zero, AddZeroClass.zero_add] at h0ex
  have ceyz : (bevalBasis m).repr a ey = 0 :=
    (mul_eq_zero.mp h0ex).resolve_right (by norm_num)
  have h0e1 : coordLm e1 ((WA x y) a) = 0 := by
    rw [hWa]
    exact map_zero (coordLm e1)
  rw [W_coord_split x y e1 ex ey ew a hd1 hd2 hd3 e1
      (fun i hi => hfresh i hi e1 hje1)] at h0e1
  have pe11 : coordLm e1 ((WA x y) (beval e1)) = 0 := by
    rw [he1, hW1, map_add]
    rcases hxyw with hc | hc
    · rw [hc, ← hew, coord_val_ne ew e1 (Ne.symm he1w)]
      norm_num
    · rw [hc, coord_neg, ← hew, coord_val_ne ew e1 (Ne.symm he1w)]
      norm_num
  have pe1x : coordLm e1 ((WA x y) (beval ex)) = 0 := by
    rw [hex, hWx, map_add, coord_neg, ← hey, coord_val_ne ey e1 (Ne.symm he1y)]
    norm_num
  have pe1y : coordLm e1 ((WA x y) (beval ey)) = 0 := by
    rw [hey, hWy, map_add, coord_neg, ← hex, coord_val_ne ex e1 (Ne.symm he1x)]
    norm_num
  obtain ⟨se1, hse1, pe1w⟩ : ∃ s : ℝ, s ≠ 0 ∧
      coordLm e1 ((WA x y) (beval ew)) = s := by
    rcases hxyw with hc | hc
    · refine ⟨2, by norm_num, ?_⟩
      rw [hew, ← hc, hWxy, ← he1, map_add, hce1]
      norm_num
    · refine ⟨-2, by norm_num, ?_⟩
      rw [hew, hwxy_neg hc, hWneg, hWxy, coord_neg, ← he1, map_add, hce1]
      norm_num
  rw [pe11, pe1x, pe1y, pe1w] at h0e1
  simp only [MulZeroClass.mul_zero, AddZeroClass.add_zero, AddZeroClass.zero_add] at h0e1
  have cewz : (bevalBasis m).repr a ew = 0 :=
    (mul_eq_zero.mp h0e1).resolve_right hse1
  exact ⟨ce1z, cexz, ceyz, cewz⟩

theorem ImagPair.Hpart_of_ker {m : ℕ} (P : ImagPair m) (a : CD m)
    (hW : (WA P.x P.y) a = (cdZero : CD m)) :
    Hpart P.e1 P.ex P.ey P.ew a = (cdZero : CD m) := by
  obtain ⟨h1, hx, hy, hw⟩ := P.ker_Hcoords a hW
  rw [Hpart_apply, coordLm_repr, coordLm_repr, coordLm_repr, coordLm_repr, h1, hx, hy, hw,
    _root_.zero_smul, _root_.zero_smul, _root_.zero_smul, _root_.zero_smul,
    AddZeroClass.zero_add, AddZeroClass.zero_add, AddZeroClass.zero_add]
  rfl

/-- S_y vanishes on every fresh sum, with no hypothesis on W. -/
theorem ImagPair.fresh_Sy {m : ℕ} (P : ImagPair m) (c : BUnit m → ℝ) :
    (∑ i ∈ Finset.univ \ ({P.e1, P.ex, P.ey, P.ew} : Finset (BUnit m)), c i • beval i) * P.y
      + P.y * ∑ i ∈ Finset.univ \ ({P.e1, P.ex, P.ey, P.ew} : Finset (BUnit m)),
          c i • beval i
      = (cdZero : CD m) := by
  rw [cd_sum_mul_left, cd_sum_mul_right, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  obtain ⟨hi1, -, hiy, -⟩ := quad_gate P.e1 P.ex P.ey P.ew i (Finset.mem_sdiff.mp hi).2
  rw [smul_mul_left', smul_mul_right', ← smul_add'',
    fresh_anticomm P.y P.e1 P.ey P.byY P.cy P.he1 P.hey i hi1 hiy]
  exact smul_zero' _

/-- S_y vanishes on L_x of every fresh sum. x sends fresh indices to
fresh indices up to sign, and each of those anticommutes with y. -/
theorem ImagPair.fresh_Sy_Lx {m : ℕ} (P : ImagPair m) (c : BUnit m → ℝ) :
    (P.x * ∑ i ∈ Finset.univ \ ({P.e1, P.ex, P.ey, P.ew} : Finset (BUnit m)),
        c i • beval i) * P.y
      + P.y * (P.x * ∑ i ∈ Finset.univ \ ({P.e1, P.ex, P.ey, P.ew} : Finset (BUnit m)),
          c i • beval i)
      = (cdZero : CD m) := by
  have hna : ∀ p q : CD m, neg p + neg q = neg (p + q) :=
    fun p q => (_root_.neg_add p q).symm
  rw [cd_sum_mul_right, cd_sum_mul_right, cd_sum_mul_left, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  obtain ⟨hi1, hix, hiy, hiw⟩ := quad_gate P.e1 P.ex P.ey P.ew i (Finset.mem_sdiff.mp hi).2
  obtain ⟨v, hv1, -, hvy, -, hs⟩ :=
    fresh_mul_left P.x P.y P.w P.e1 P.ex P.ey P.ew P.bx P.cx P.byY P.cy P.bw P.ne P.xy
      P.he1 P.hex P.hey P.hew i hi1 hix hiy hiw
  rcases hs with h | h
  · rw [smul_mul_right', smul_mul_left', smul_mul_right', ← smul_add'', h,
      fresh_anticomm P.y P.e1 P.ey P.byY P.cy P.he1 P.hey v hv1 hvy]
    exact smul_zero' _
  · rw [smul_mul_right', smul_mul_left', smul_mul_right', ← smul_add'', h,
      neg_mul, mul_neg, hna,
      fresh_anticomm P.y P.e1 P.ey P.byY P.cy P.he1 P.hey v hv1 hvy, neg_zero]
    exact smul_zero' _

/-- On the fresh complement, C∘L_x = L_x∘W. -/
theorem ImagPair.CA_Lx_eq {m : ℕ} (P : ImagPair m) (f : CD m)
    (hf : Hpart P.e1 P.ex P.ey P.ew f = (cdZero : CD m)) :
    CA P.x P.y (P.x * f) = P.x * (WA P.x P.y) f := by
  have hart : ∀ t : CD m, P.x * (P.x * t) = neg t := by
    intro t
    rw [P.artLx t, P.sqx, neg_one_mul]
  have hfresh := P.eq_fresh_sum f hf
  have hS0 : f * P.y + P.y * f = (cdZero : CD m) := by
    rw [hfresh]
    exact P.fresh_Sy fun i => (bevalBasis m).repr f i
  have hS1 : (P.x * f) * P.y + P.y * (P.x * f) = (cdZero : CD m) := by
    rw [hfresh]
    exact P.fresh_Sy_Lx fun i => (bevalBasis m).repr f i
  have ebar : conj P.x * (P.x * f) = f := by
    rw [P.cx, neg_mul, hart f, neg_neg]
  have eS0 : P.y * f = neg (f * P.y) := by
    rw [add_comm] at hS0
    exact eq_neg_of_add_eq_zero_left hS0
  have eS1 : P.y * (P.x * f) = neg ((P.x * f) * P.y) := by
    rw [add_comm] at hS1
    exact eq_neg_of_add_eq_zero_left hS1
  have hL : CA P.x P.y (P.x * f) = neg (f * P.y) + P.x * ((P.x * f) * P.y) := by
    rw [CA_apply, ebar, P.cx, neg_mul, eS1, mul_neg, neg_neg, eS0]
  have hR : P.x * (WA P.x P.y) f = neg (f * P.y) + P.x * ((P.x * f) * P.y) := by
    have hWA : (WA P.x P.y) f = (P.x * f) * P.y + P.x * (f * P.y) := rfl
    rw [hWA, mul_add', hart (f * P.y), add_comm]
  rw [hL, hR]

/-- The four H-coordinates, as one linear map into `ℝ × ℝ × ℝ × ℝ`. -/
noncomputable def ImagPair.hCoeffs {m : ℕ} (P : ImagPair m) :
    CD m →ₗ[ℝ] ℝ × ℝ × ℝ × ℝ :=
  LinearMap.prod (coordLm P.e1)
    (LinearMap.prod (coordLm P.ex)
      (LinearMap.prod (coordLm P.ey) (coordLm P.ew)))

/-- The linear combination those four coordinates name. -/
noncomputable def ImagPair.coeffTo {m : ℕ} (P : ImagPair m) :
    ℝ × ℝ × ℝ × ℝ →ₗ[ℝ] CD m :=
  LinearMap.coprod (LinearMap.toSpanSingleton ℝ (CD m) (beval P.e1))
    (LinearMap.coprod (LinearMap.toSpanSingleton ℝ (CD m) (beval P.ex))
      (LinearMap.coprod (LinearMap.toSpanSingleton ℝ (CD m) (beval P.ey))
        (LinearMap.toSpanSingleton ℝ (CD m) (beval P.ew))))

theorem ImagPair.CA_e1 {m : ℕ} (P : ImagPair m) :
    CA P.x P.y (beval P.e1) = (cdZero : CD m) := by
  rw [CA_apply, P.he1]
  exact C_ker_one P.x P.y P.cx (basisUnit_anticomm P.bx P.byY P.cx P.cy P.ne)

theorem ImagPair.CA_ex {m : ℕ} (P : ImagPair m) :
    CA P.x P.y (beval P.ex) = (cdZero : CD m) := by
  rw [CA_apply, P.hex]
  exact C_ker_x P.x P.y P.cx P.sqx (basisUnit_anticomm P.bx P.byY P.cx P.cy P.ne)
    (fun t => P.artLx t)

theorem ImagPair.CA_ey {m : ℕ} (P : ImagPair m) :
    CA P.x P.y (beval P.ey) = (cdZero : CD m) := by
  rw [CA_apply, P.hey]
  exact C_ker_y P.x P.y P.cx P.sqy P.hyxy (fun t => P.artRy t)

theorem ImagPair.CA_exy {m : ℕ} (P : ImagPair m) :
    CA P.x P.y (P.x * P.y) = (cdZero : CD m) := by
  rw [CA_apply]
  exact C_ker_xy P.x P.y P.cx P.sqx P.sqy P.hyxy (fun t => P.artLx t) (fun t => P.artRy t)

theorem ImagPair.CA_ew {m : ℕ} (P : ImagPair m) :
    CA P.x P.y (beval P.ew) = (cdZero : CD m) := by
  rcases P.xy with hc | hc
  · rw [P.hew, ← hc]
    exact P.CA_exy
  · rw [P.hew, P.w_of_neg hc]
    have hneg : CA P.x P.y (neg (P.x * P.y)) = neg (CA P.x P.y (P.x * P.y)) :=
      map_neg (CA P.x P.y) (P.x * P.y)
    rw [hneg, P.CA_exy]
    exact neg_zero

theorem ImagPair.CA_coeff {m : ℕ} (P : ImagPair m) (c : ℝ × ℝ × ℝ × ℝ) :
    CA P.x P.y (P.coeffTo c) = (cdZero : CD m) := by
  rcases c with ⟨c1, cx, cy, cw⟩
  simp only [ImagPair.coeffTo, LinearMap.coprod_apply, LinearMap.toSpanSingleton,
    LinearMap.smulRight_apply, LinearMap.id_apply, map_add, map_smul,
    P.CA_e1, P.CA_ex, P.CA_ey, P.CA_ew, smul_zero', zero_add]

/-- Left multiplication by x permutes the H-span, so C still kills it. -/
theorem ImagPair.CA_Lx_coeff {m : ℕ} (P : ImagPair m) (c : ℝ × ℝ × ℝ × ℝ) :
    CA P.x P.y (P.x * P.coeffTo c) = (cdZero : CD m) := by
  rcases c with ⟨c1, cx, cy, cw⟩
  have hneg : ∀ v : CD m, CA P.x P.y (neg v) = neg (CA P.x P.y v) :=
    fun v => map_neg (CA P.x P.y) v
  have h1 : P.x * beval P.e1 = beval P.ex := by rw [P.he1, P.hex, mul_one]
  have hx : P.x * beval P.ex = neg (beval P.e1) := by rw [P.hex, P.he1, P.sqx]
  have hy : P.x * beval P.ey = P.x * P.y := by rw [P.hey]
  have hsum : P.x * P.coeffTo ⟨c1, cx, cy, cw⟩ =
      c1 • (P.x * beval P.e1) + (cx • (P.x * beval P.ex)
        + (cy • (P.x * beval P.ey) + cw • (P.x * beval P.ew))) := by
    simp only [ImagPair.coeffTo, LinearMap.coprod_apply, LinearMap.toSpanSingleton,
      LinearMap.smulRight_apply, LinearMap.id_apply, mul_add', smul_mul_right']
  rw [hsum, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, hx, hy]
  rcases P.xy with hc | hc
  · have hw : P.x * beval P.ew = neg (beval P.ey) := by
      rw [P.hew, ← hc, P.artLx P.y, P.sqx, neg_one_mul, P.hey]
    rw [hw]
    simp only [hneg, P.CA_e1, P.CA_ex, P.CA_ey, P.CA_exy, neg_zero, smul_zero', zero_add]
  · have hw : P.x * beval P.ew = beval P.ey := by
      rw [P.hew, P.w_of_neg hc, mul_neg, P.artLx P.y, P.sqx, neg_one_mul, neg_neg, P.hey]
    rw [hw]
    simp only [hneg, P.CA_e1, P.CA_ex, P.CA_ey, P.CA_exy, neg_zero, smul_zero', zero_add]

theorem finrank_R4 : Module.finrank ℝ (ℝ × ℝ × ℝ × ℝ) = 4 := by
  simp [Module.finrank_prod, Module.finrank_self]

theorem ImagPair.hCoeffs_coeffTo {m : ℕ} (P : ImagPair m) :
    P.hCoeffs.comp P.coeffTo = LinearMap.id := by
  apply LinearMap.ext
  intro c
  rcases c with ⟨c1, cx, cy, cw⟩
  have hto : P.coeffTo ⟨c1, cx, cy, cw⟩ =
      c1 • beval P.e1 + (cx • beval P.ex
        + (cy • beval P.ey + cw • beval P.ew)) := by
    simp only [ImagPair.coeffTo, LinearMap.coprod_apply, LinearMap.toSpanSingleton,
      LinearMap.smulRight_apply, LinearMap.id_apply]
  have hcoord (j : BUnit m) :
      coordLm j (P.coeffTo ⟨c1, cx, cy, cw⟩) =
        c1 * coordLm j (beval P.e1) + (cx * coordLm j (beval P.ex)
          + (cy * coordLm j (beval P.ey) + cw * coordLm j (beval P.ew))) := by
    rw [hto, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  simp only [ImagPair.hCoeffs, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.prod_apply, Function.prod_apply]
  apply Prod.ext
  · rw [hcoord P.e1, coord_apply, coord_val_ne P.ex P.e1 (Ne.symm P.he1x),
        coord_val_ne P.ey P.e1 (Ne.symm P.he1y),
        coord_val_ne P.ew P.e1 (Ne.symm P.he1w), if_pos rfl]
    ring
  · apply Prod.ext
    · rw [hcoord P.ex, coord_val_ne P.e1 P.ex P.he1x, coord_apply,
          coord_val_ne P.ey P.ex (Ne.symm P.hexy),
          coord_val_ne P.ew P.ex (Ne.symm P.hexw), if_pos rfl]
      ring
    · apply Prod.ext
      · rw [hcoord P.ey, coord_val_ne P.e1 P.ey P.he1y, coord_val_ne P.ex P.ey P.hexy,
            coord_apply, coord_val_ne P.ew P.ey (Ne.symm P.heyw), if_pos rfl]
        ring
      · rw [hcoord P.ew, coord_val_ne P.e1 P.ew P.he1w, coord_val_ne P.ex P.ew P.hexw,
            coord_val_ne P.ey P.ew P.heyw, coord_apply, if_pos rfl]
        ring

theorem ImagPair.hCoeffs_coeffTo_apply {m : ℕ} (P : ImagPair m)
    (c : ℝ × ℝ × ℝ × ℝ) : P.hCoeffs (P.coeffTo c) = c :=
  LinearMap.congr_fun P.hCoeffs_coeffTo c

theorem ImagPair.Hpart_eq {m : ℕ} (P : ImagPair m) :
    Hpart P.e1 P.ex P.ey P.ew = P.coeffTo.comp P.hCoeffs := by
  apply LinearMap.ext
  intro a
  rw [Hpart_apply, LinearMap.comp_apply]
  simp only [ImagPair.hCoeffs, ImagPair.coeffTo, LinearMap.prod_apply, Function.prod_apply,
    LinearMap.coprod_apply, LinearMap.toSpanSingleton, LinearMap.smulRight_apply,
    LinearMap.id_apply]

/-- (c, k) ↦ x·(coeff(c) + k), landing in ker C. -/
noncomputable def ImagPair.foldSeed {m : ℕ} (P : ImagPair m) :
    (ℝ × ℝ × ℝ × ℝ) × LinearMap.ker (WA P.x P.y) →ₗ[ℝ] LinearMap.ker (CA P.x P.y) :=
  LinearMap.codRestrict (LinearMap.ker (CA P.x P.y))
    ((mulLeft P.x).comp
      (LinearMap.coprod P.coeffTo (LinearMap.ker (WA P.x P.y)).subtype))
    (fun p => by
      rcases p with ⟨c, k⟩
      have hk : Hpart P.e1 P.ex P.ey P.ew k.1 = (cdZero : CD m) :=
        P.Hpart_of_ker k.1 k.2
      have hC1 : CA P.x P.y (P.x * P.coeffTo c) = (cdZero : CD m) := P.CA_Lx_coeff c
      have hC2 : CA P.x P.y (P.x * k.1) = P.x * (WA P.x P.y) k.1 := P.CA_Lx_eq k.1 hk
      have hk0 : (WA P.x P.y) k.1 = (cdZero : CD m) := k.2
      rw [hk0, mul_zero] at hC2
      have hsplit : P.x * (P.coeffTo c + k.1) = P.x * P.coeffTo c + P.x * k.1 :=
        mul_add' P.x (P.coeffTo c) k.1
      show CA P.x P.y (P.x * (P.coeffTo c + k.1)) = (cdZero : CD m)
      rw [hsplit, map_add, hC1, hC2, add_zero])

theorem ImagPair.foldSeed_injective {m : ℕ} (P : ImagPair m) :
    Function.Injective (P.foldSeed) := by
  intro p q hpq
  rcases p with ⟨c, k⟩
  rcases q with ⟨c', k'⟩
  have h := congrArg (fun z : LinearMap.ker (CA P.x P.y) => (z : CD m)) hpq
  simp only [ImagPair.foldSeed, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    LinearMap.coprod_apply, Submodule.subtype_apply] at h
  have hinj := (P.Lx).injective h
  have hck : Hpart P.e1 P.ex P.ey P.ew k.1 = (cdZero : CD m) := P.Hpart_of_ker k.1 k.2
  have hck' : Hpart P.e1 P.ex P.ey P.ew k'.1 = (cdZero : CD m) := P.Hpart_of_ker k'.1 k'.2
  have hHc : Hpart P.e1 P.ex P.ey P.ew (P.coeffTo c) = P.coeffTo c := by
    rw [P.Hpart_eq, LinearMap.comp_apply, P.hCoeffs_coeffTo_apply]
  have hHc' : Hpart P.e1 P.ex P.ey P.ew (P.coeffTo c') = P.coeffTo c' := by
    rw [P.Hpart_eq, LinearMap.comp_apply, P.hCoeffs_coeffTo_apply]
  have hsum := congrArg (Hpart P.e1 P.ex P.ey P.ew) hinj
  rw [map_add, map_add, hHc, hHc', hck, hck', add_zero, add_zero] at hsum
  have hc : c = c' := by
    have hcc := congrArg P.hCoeffs hsum
    rw [P.hCoeffs_coeffTo_apply, P.hCoeffs_coeffTo_apply] at hcc
    exact hcc
  subst hc
  exact Prod.ext rfl (Subtype.ext (add_left_cancel' hinj))

theorem WT_dbl {m : ℕ} (x y a₀ a₁ : CD m) :
    WT x y (dbl a₀ a₁) = dbl ((WA x y) a₀) ((CA x y) a₁) :=
  W_block x y a₀ a₁

theorem ImagPair.foldSeed_surjective {m : ℕ} (P : ImagPair m) :
    Function.Surjective (P.foldSeed) := by
  intro u
  let a : CD m := P.Lx.symm (u : CD m)
  let c : ℝ × ℝ × ℝ × ℝ := P.hCoeffs a
  let f : CD m := a - P.coeffTo c
  have ha : P.x * a = (u : CD m) := P.Lx.apply_symm_apply (u : CD m)
  have hHa : Hpart P.e1 P.ex P.ey P.ew a = P.coeffTo c := by
    rw [P.Hpart_eq, LinearMap.comp_apply]
  have hHc : Hpart P.e1 P.ex P.ey P.ew (P.coeffTo c) = P.coeffTo c := by
    rw [P.Hpart_eq, LinearMap.comp_apply, P.hCoeffs_coeffTo_apply]
  have hfH : Hpart P.e1 P.ex P.ey P.ew f = (cdZero : CD m) := by
    have hsub : Hpart P.e1 P.ex P.ey P.ew f
        = Hpart P.e1 P.ex P.ey P.ew a - Hpart P.e1 P.ex P.ey P.ew (P.coeffTo c) :=
      map_sub (Hpart P.e1 P.ex P.ey P.ew) a (P.coeffTo c)
    rw [hsub, hHa, hHc, sub_add, add_comm, neg_add_self]
  have hxf : P.x * f = (u : CD m) + neg (P.x * P.coeffTo c) := by
    have hf : f = a + neg (P.coeffTo c) := sub_add a (P.coeffTo c)
    rw [hf, mul_add', ha, mul_neg]
  have hCu : CA P.x P.y (P.x * f) = (cdZero : CD m) := by
    have hneg : CA P.x P.y (neg (P.x * P.coeffTo c))
        = neg (CA P.x P.y (P.x * P.coeffTo c)) :=
      map_neg (CA P.x P.y) (P.x * P.coeffTo c)
    have hu0 : CA P.x P.y (u : CD m) = (cdZero : CD m) := u.2
    rw [hxf, map_add, hneg, P.CA_Lx_coeff c, neg_zero, hu0, zero_add]
  have hCeq := P.CA_Lx_eq f hfH
  rw [hCu] at hCeq
  have hinv : neg P.x * (P.x * (WA P.x P.y) f) = (WA P.x P.y) f := by
    simpa [LinearMap.comp_apply, mulLeft, LinearMap.id_apply] using
      LinearMap.congr_fun (basisUnit_mulLeft_left_inv P.bx P.cx) ((WA P.x P.y) f)
  rw [← hCeq, mul_zero] at hinv
  have hWf : (WA P.x P.y) f = (cdZero : CD m) := hinv.symm
  have hrec : P.coeffTo c + f = a := by
    have hf : f = a + neg (P.coeffTo c) := sub_add a (P.coeffTo c)
    rw [hf, add_comm (P.coeffTo c), add_assoc, neg_add_self, add_zero]
  refine ⟨(c, ⟨f, hWf⟩), ?_⟩
  apply Subtype.ext
  show P.x * (P.coeffTo c + f) = (u : CD m)
  rw [hrec, ha]

theorem ImagPair.finrank_ker_CA {m : ℕ} (P : ImagPair m) :
    Module.finrank ℝ (LinearMap.ker (CA P.x P.y))
      = 4 + Module.finrank ℝ (LinearMap.ker (WA P.x P.y)) := by
  let e := LinearEquiv.ofBijective P.foldSeed
    ⟨P.foldSeed_injective, P.foldSeed_surjective⟩
  have h := e.finrank_eq
  rw [Module.finrank_prod, finrank_R4] at h
  exact h.symm

theorem finrank_ker_CA {m : ℕ} (x y : CD m)
    (hbx : BasisUnit x) (hcx : conj x = neg x)
    (hby : BasisUnit y) (hcy : conj y = neg y) (hne : x ≠ y) :
    Module.finrank ℝ (LinearMap.ker (CA x y))
      = 4 + Module.finrank ℝ (LinearMap.ker (WA x y)) := by
  obtain ⟨P, rfl, rfl⟩ := ImagPair.exists_eq x y hbx hcx hby hcy hne
  exact P.finrank_ker_CA

theorem ker_WTP_prod {m : ℕ} (x y : CD m) :
    LinearMap.ker (WTP x y)
      = (LinearMap.ker (WA x y)).prod (LinearMap.ker (CA x y)) := by
  ext p
  rcases p with ⟨a, b⟩
  simp only [Submodule.mem_prod, LinearMap.mem_ker]
  have hblock : WTP x y (a, b) = dbl ((WA x y) a) ((CA x y) b) := by
    show WT x y (dbl a b) = dbl ((WA x y) a) ((CA x y) b)
    exact WT_dbl x y a b
  constructor
  · intro h
    rw [hblock] at h
    have h0 : dbl ((WA x y) a) ((CA x y) b) = dbl (cdZero : CD m) cdZero := h
    injection h0 with _ h1 h2
    exact ⟨h1, h2⟩
  · intro h
    rw [hblock, h.1, h.2]
    rfl

/-- Off full alternativity: dim ker W_{m+1} = 2·dim ker W_m + 4,
for every pair of distinct imaginary basis units. -/
theorem finrank_ker_WT_fold {m : ℕ} (x y : CD m)
    (hbx : BasisUnit x) (hcx : conj x = neg x)
    (hby : BasisUnit y) (hcy : conj y = neg y) (hne : x ≠ y) :
    Module.finrank ℝ (LinearMap.ker (WT x y))
      = 2 * Module.finrank ℝ (LinearMap.ker (WA x y)) + 4 := by
  have hker := ker_WTP_prod x y
  have h5 : LinearMap.range (WTP x y) = LinearMap.range (WT x y) := by
    ext v
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨cdPairLm p, hp⟩
    · rintro ⟨u, hu⟩
      obtain ⟨p, hp⟩ := cdPairLm_surjective u
      exact ⟨p, by
        have hg : WT x y (cdPairLm p) = v := by rw [hp]; exact hu
        exact hg⟩
  have h6 := LinearMap.finrank_range_add_finrank_ker (WTP x y)
  have h7 := LinearMap.finrank_range_add_finrank_ker (WT x y)
  rw [h5, Module.finrank_prod, finrank_cd] at h6
  rw [finrank_cd, pow_succ, Nat.mul_two] at h7
  have hdim : Module.finrank ℝ (LinearMap.ker (WTP x y))
      = Module.finrank ℝ (LinearMap.ker (WA x y))
        + Module.finrank ℝ (LinearMap.ker (CA x y)) := by
    rw [hker, LinearEquiv.finrank_eq
        (Submodule.prodEquiv (LinearMap.ker (WA x y)) (LinearMap.ker (CA x y))),
      Module.finrank_prod]
  have hCA := finrank_ker_CA x y hbx hcx hby hcy hne
  have hkerEq : Module.finrank ℝ (LinearMap.ker (WT x y))
      = Module.finrank ℝ (LinearMap.ker (WTP x y)) := by
    omega
  rw [hkerEq, hdim, hCA]
  omega

/-!
### Seal (2026-10-01)

The fold-law chain through chain steps (1)-(5) plus the fold law in
kernel form is sorry-free: alternativity of ℍ→ℍ-doubles (R→ℂ→ℍ→𝕆),
the kernel isomorphism ker L_z ≅ ker W with the numeric octonion
anchor z = i + jℓ, the diagonal block lemma ker W_T = ker W_A ⊕ ker C
with C = -{L_x, L_y}, the quaternion containment
H = span{1, x, y, xy} ⊂ ker C with the octonionic anchor for (i, j),
x·ker W ⊆ ker C in the pointwise form C∘L_x = 0 (a fortiori on
ker W) with the octonionic anchor, and the directness engine of
H ∩ x·ker W = 0: L_x injective by the left art plus the numeric
anchor ker W(i, j) = 0 at the ℍ rung where H(i, j) is all of ℍ; and
the fold law itself: L_x is surjective constructively (u = x·(x̄u)),
hence C ≡ 0 identically at art levels, hence ker W_{m+1} = ker W_m ⊕
(free ℓ-block), anchored at the (i, j)-rung as the 16-census value 4
and by art at CD 3 as the 32-census value 12 for old pairs.
The finrank layer closes the chain as EQUATIONS BETWEEN NUMBERS:
CD m is a genuine R-module (componentwise scalar recursion, the scalar
passes through the multiplication on either side), finrank (CD m) = 2^m,
W_A and W_T are linear maps, and rank-nullity turns the kernel
decomposition into dim ker W_{m+1} = dim ker W_m + 2^m -- anchored at
dim ker W(i, j)|ℍ = 0, this machine-checks the census values 4 (16) and
12 (32) as closed numerals, sorry-free.
Beyond that rung the algebra is not alternative, but every standard basis
unit still is: `basisUnit_left_art` and `basisUnit_right_art` hold at every
level, by induction on the basis (the real unit, the lower slot, the upper
slot). Full alternativity is used only by `art_left_lin`, which polarises
onto the sum of two units; a single basis unit never needs it. For the
centre pair (i, j) embedded into every higher level, `C_ker_H_centre`
puts the whole quaternion H inside ker C, using that unit art.
For this pair the complementary block vanishes outright, not only on H:
`C_embed` splits C of a lower embedding into (C(u), C(v)), so the
quaternion vanishing `C_eq_zero` lifts by induction (`C_zero_centre`)
past the death of alternativity. With the second block free,
`finrank_ker_centre` is the maximum at every height:
dim ker W(embed^k i, embed^k j) = 2^{2+k} − 4
(0, 4, 12, 28, 60, …). A generic pair is not this pair: off the
maximum, C does not vanish. Step (5) for a general pair is half done:
`W_val_one/x/y/xy` send the quaternion basis to twice itself up to sign
and `xbar_stab_*` keep `conj x` inside its span, all with unit-level art
only — the computation half of H ∩ x·ker W = 0. ker W is stable under
L_x and R_y with unit art only (`W_stable_Lx/Ry`), and the weak inclusion
is reduced to the two symmetric-part vanishings (`C_of_W_of_S`).
Basis floor 1 is in: `cdOne_ne_neg_one`, `basisUnit_conj`, and distinct
imaginary basis units anticommuting (`basisUnit_anticomm`), all by
tower induction with no coordinates. Floor 2 is in: products of basis
units stay basis up to sign (`basisUnit_mul_closed`, by level induction
— upper-lower needs the full rung-below hypothesis with swapped
factors). Floor 3 is in: no basis unit is zero (`basisUnit_ne_zero`),
lower and upper slots never meet (`lower_ne_upper`), and distinct
imaginary basis units multiply to a FRESH imaginary basis unit up to
sign — never ±1, never either factor (`basisUnit_mul_distinct`, level
induction; the obtain pattern splits the product disjunction into an
`= w` and an `= −w` branch at the point of destructing). Floor 3½ is
in: the cancellation laws — if x·u lands on ±y then u is already ±w
(`basisUnit_cancel_left/right`, via unit art only), with the
companions x·w = ±y, w·y = ±x, y·w = ±x (`basisUnit_xw/wy/yw`) and
the sign utilities `neg_one_mul`, `mul_neg_one`, `neg_inj`,
`basisUnit_sq`. These are the exact gates the H^⊥-invariance of W
will pass through.
`#print axioms` below must show only the three standard axioms of Lean's
dependent type theory (propext, Classical.choice, Quot.sound) -- no
`sorryAx`, no hand-added `axiom` decls.
-/

#print axioms assoc_succ_of_comm
#print axioms assoc_one
#print axioms assoc_two
#print axioms art_left_of_assoc
#print axioms art_right_of_assoc
#print axioms art_left_three
#print axioms art_right_three
#print axioms ker_Lz_iff_ker_W
#print axioms ker_Lz_octonion
#print axioms W_block
#print axioms ker_WT_iff
#print axioms C_eq_neg_anticommutator
#print axioms neg_dbl
#print axioms C_ker_one
#print axioms C_ker_x
#print axioms C_ker_y
#print axioms C_ker_xy
#print axioms unitI_mul_unitJ
#print axioms unitJ_mul_unitI
#print axioms hxy_units
#print axioms hyxy_units
#print axioms C_ker_H_octonion
#print axioms add_left_cancel
#print axioms add_right_cancel
#print axioms art_left_lin
#print axioms C_comp_Lx_eq_zero
#print axioms x_mul_ker_W_subset_ker_C
#print axioms C_comp_Lx_octonion
#print axioms add_self_eq_zero
#print axioms Lx_inj
#print axioms W_inj_quaternion
#print axioms x_mul_kerW_inter_H_octonion
#print axioms Lx_surj
#print axioms C_eq_zero
#print axioms ker_W_fold
#print axioms ker_W_octonion_fold
#print axioms finrank_cd
#print axioms WA_eq_WT_embed
#print axioms ker_WTP_eq
#print axioms finrank_ker_W_fold
#print axioms WA_quaternion_injective
#print axioms finrank_ker_WT_octonion
#print axioms conj_unitI'
#print axioms unitI_sq'
#print axioms hxy_units'
#print axioms finrank_ker_WT_sedenion
#print axioms basisUnit_cdOne
#print axioms basisUnit_left_art
#print axioms basisUnit_right_art
#print axioms centre_hyp
#print axioms C_ker_H_centre
#print axioms C_embed
#print axioms C_zero_centre
#print axioms finrank_ker_of_C_zero
#print axioms finrank_ker_centre
#print axioms xbar_stab_one
#print axioms xbar_stab_x
#print axioms xbar_stab_y
#print axioms xbar_stab_xy
#print axioms W_val_one
#print axioms W_val_x
#print axioms W_val_y
#print axioms W_val_xy
#print axioms W_stable_Lx
#print axioms W_stable_Ry
#print axioms C_of_W_of_S
#print axioms cdOne_ne_neg_one
#print axioms cdZero_sub
#print axioms basisUnit_conj
#print axioms conj_lower
#print axioms basisUnit_anticomm
#print axioms basisUnit_mul_closed_aux
#print axioms basisUnit_mul_closed
#print axioms basisUnit_ne_zero
#print axioms lower_ne_upper
#print axioms basisUnit_mul_distinct_aux
#print axioms basisUnit_mul_distinct
#print axioms neg_one_mul
#print axioms mul_neg_one
#print axioms neg_inj
#print axioms basisUnit_sq
#print axioms basisUnit_cancel_core
#print axioms basisUnit_cancel_left
#print axioms basisUnit_cancel_right
#print axioms basisUnit_xw
#print axioms basisUnit_wy
#print axioms basisUnit_yw
#print axioms beval_basis
#print axioms beval_inj
#print axioms basisUnit_beval
#print axioms bUnit_card
#print axioms cdZero_add_cdZero
#print axioms smul_zero'
#print axioms smul_dbl
#print axioms sum_dbl_lower
#print axioms sum_dbl_upper
#print axioms sum_lower_split
#print axioms sum_upper_split
#print axioms beval_linearIndependent
#print axioms cdOne_ne_zero
#print axioms bevalBasis
#print axioms beval_neg_inj
#print axioms basisUnit_neg_not
#print axioms fresh_anticomm
#print axioms fresh_mul_left
#print axioms bevalBasis_apply
#print axioms a_decomp
#print axioms fresh_mul_right
#print axioms coord_apply
#print axioms coord_val_ne
#print axioms coord_neg
#print axioms fresh_W_coord_zero
#print axioms W_coord_split
#print axioms weak_inclusion
#print axioms basisUnit_mulLeft_right_inv
#print axioms basisUnit_mulLeft_left_inv
#print axioms CA_apply
#print axioms quad_mem
#print axioms quad_gate
#print axioms quad_jor
#print axioms coordLm_repr
#print axioms Hpart_apply
#print axioms Hset_sum_eq
#print axioms ImagPair.sqx
#print axioms ImagPair.sqy
#print axioms ImagPair.artLx
#print axioms ImagPair.artRy
#print axioms ImagPair.hyxy
#print axioms ImagPair.w_of_neg
#print axioms ImagPair.exists_eq
#print axioms ImagPair.Hsum_eq_Hpart
#print axioms ImagPair.eq_fresh_sum
#print axioms ImagPair.ker_Hcoords
#print axioms ImagPair.Hpart_of_ker
#print axioms ImagPair.fresh_Sy
#print axioms ImagPair.fresh_Sy_Lx
#print axioms ImagPair.CA_Lx_eq
#print axioms ImagPair.CA_e1
#print axioms ImagPair.CA_ex
#print axioms ImagPair.CA_ey
#print axioms ImagPair.CA_exy
#print axioms ImagPair.CA_ew
#print axioms ImagPair.CA_coeff
#print axioms ImagPair.CA_Lx_coeff
#print axioms finrank_R4
#print axioms ImagPair.hCoeffs_coeffTo
#print axioms ImagPair.hCoeffs_coeffTo_apply
#print axioms ImagPair.Hpart_eq
#print axioms ImagPair.foldSeed_injective
#print axioms WT_dbl
#print axioms ImagPair.foldSeed_surjective
#print axioms ImagPair.finrank_ker_CA
#print axioms finrank_ker_CA
#print axioms ker_WTP_prod
#print axioms finrank_ker_WT_fold

end Foldlaw