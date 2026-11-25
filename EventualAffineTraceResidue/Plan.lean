/-
Copyright (c) 2026 benkeene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: benkeene
-/
module

public import Mathlib
public import EventualAffineTraceResidue.Basic

/-!
# Eventual affine trace residue: the lattice plan

The planned development of PROOF.md. The record definitions (`shiftedSemigroup`, `pseudoFrobenius`,
`trace`, `traceResidue`) are those of `EventualAffineTraceResidue.Basic`. The statement of record is
proved here as `trace_residue_eventually_affine_dev`; `Solution.lean` bridges to it.
-/

@[expose] public section

namespace EventualAffineTraceResidue

namespace Plan

-- PROOF.md 13, 242, 272.
structure Data where
  k : ℕ
  hk : 1 ≤ k
  r : Fin (k + 1) → ℤ
  w : ℤ
  n : ℤ
  hr0 : r 0 = 0
  hr : StrictMono r
  hw : r (Fin.last k) = w
  hn : 0 < n
  hnd : Int.gcd n (Finset.univ.gcd fun i : Fin k => r i.succ) = 1

abbrev Point := ℤ × ℤ
def d (p : Data) : ℤ := Finset.univ.gcd fun i : Fin p.k => p.r i.succ
def m (p : Data) (l : ℤ) : ℤ := p.n + l * p.w
def M (p : Data) (l : ℤ) : ℤ := m p l + p.w
def H (p : Data) (l : ℤ) : Set ℤ := shiftedSemigroup p.k p.r p.n p.w l

-- PROOF.md 17-26.
def sums (p : Data) (s : ℕ) : Set ℤ :=
  {a | ∃ f : Fin s → Fin (p.k + 1), ∑ j, p.r (f j) = a}
def S (p : Data) : AddSubmonoid ℤ := AddSubmonoid.closure (Set.range p.r)
def Sr (p : Data) : AddSubmonoid ℤ :=
  AddSubmonoid.closure (Set.range fun i => p.w - p.r i)
def lattice (p : Data) : Set Point :=
  {y | d p ∣ y.1 ∧ d p ∣ y.2 ∧ p.w ∣ y.1 + y.2}
def coset (p : Data) : Set Point :=
  {z | d p ∣ z.1 ∧ d p ∣ z.2 ∧ p.w ∣ z.1 + z.2 + d p * p.n}
def g (p : Data) (i : Fin (p.k + 1)) : Point := (p.r i, p.w - p.r i)
def T (p : Data) : AddSubmonoid Point := AddSubmonoid.closure (Set.range (g p))
def star (p : Data) : Set Point := {y | y ∈ lattice p ∧ y.1 ∈ S p ∧ y.2 ∈ Sr p}
def proj (p : Data) (l : ℤ) (y : Point) : ℤ :=
  (y.1 * M p l + y.2 * m p l) / p.w
def v (p : Data) (l : ℤ) : Point := (-d p * m p l, d p * M p l)
def P (p : Data) (l : ℤ) : Point := (0, d p * M p l)
def chi (p : Data) (l : ℤ) (y : Point) : Prop := proj p l y ∈ H p l
def strip (p : Data) (l : ℤ) : Set Point :=
  {y | y ∈ lattice p ∧ 0 ≤ y.1 ∧ y.1 < d p * m p l}
def positiveStrip (p : Data) (l : ℤ) : Set Point := {y | y ∈ strip p l ∧ 0 ≤ y.2}

-- PROOF.md 13-18, 44.
theorem arithmetic (p : Data) :
    0 < d p ∧ 0 < p.w ∧ d p ∣ p.w ∧
    (∀ i, 0 ≤ p.r i ∧ p.r i ≤ p.w ∧ d p ∣ p.r i) ∧
    ∀ l : ℤ, 0 ≤ l → 0 < m p l ∧ Int.gcd (m p l) (d p) = 1 := by
  sorry

-- PROOF.md 18; the conductor is arbitrary, not necessarily least.
structure Conductor (p : Data) where
  c : ℤ
  nonneg : 0 ≤ c
  dvd : d p ∣ c
  covers : ∀ x : ℤ, d p ∣ x → c ≤ x → x ∈ S p ∧ x ∈ Sr p

theorem conductor_exists (p : Data) : Nonempty (Conductor p) := by
  sorry

-- PROOF.md 44, 49, 53.
theorem monoid_model (p : Data) :
    (∀ y : Point, y ∈ T p ↔ ∃ s : ℕ, y.1 ∈ sums p s ∧ y.2 = s * p.w - y.1) ∧
    (∀ y ∈ T p, y ∈ star p) ∧
    (∀ a ∈ S p, 0 ≤ a ∧ d p ∣ a) ∧
    (∀ b ∈ Sr p, 0 ≤ b ∧ d p ∣ b) := by
  sorry

-- PROOF.md 36-46, 24. No additivity is asserted off the lattice.
theorem lattice_model (p : Data) (l : ℤ) (hl : 0 ≤ l) :
    (∀ x ∈ lattice p, ∀ y ∈ lattice p, proj p l (x + y) = proj p l x + proj p l y) ∧
    (∀ x : ℤ, ∃ y ∈ lattice p, proj p l y = x) ∧
    (∀ y ∈ lattice p, proj p l y = 0 ↔ ∃ j : ℤ, y = j • v p l) ∧
    (∀ i, proj p l (g p i) = m p l + p.r i) ∧
    H p l = Set.image (proj p l) (T p : Set Point) ∧
    (∀ z : Point, z ∈ coset p ↔ P p l + z ∈ lattice p) := by
  sorry

theorem membership_and_lifts (p : Data) (l : ℤ) (hl : 0 ≤ l) :
    (∀ y ∈ lattice p, chi p l y ↔ ∃ j : ℤ, y + j • v p l ∈ T p) ∧
    (∀ y ∈ lattice p, ∀ j : ℤ, chi p l (y + j • v p l) ↔ chi p l y) ∧
    Set.BijOn (proj p l) (strip p l) Set.univ := by
  sorry

-- PROOF.md 28, 37, 44, 148.
theorem numerical_and_pf_test (p : Data) (l : ℤ) (hl : 0 ≤ l) :
    (∀ h ∈ H p l, 0 ≤ h) ∧
    (∃ C : ℤ, ∀ h : ℤ, C ≤ h → h ∈ H p l) ∧
    (∀ x : ℤ, x ∈ pseudoFrobenius (H p l) ↔
      x ∉ H p l ∧ ∀ i, x + m p l + p.r i ∈ H p l) := by
  sorry

-- PROOF.md 50, 55-65. This quotient is exact since d divides c and w.
def s0 (p : Data) (b : Conductor p) : ℤ := 2 * (b.c + p.w) / d p

theorem bounded_length (p : Data) (b : Conductor p) :
    (∀ a ∈ S p, ∃ s : ℕ, a ∈ sums p s ∧
      (s : ℤ) * p.w ≤ a + ((b.c + p.w) / d p) * p.w) ∧
    (∀ a ∈ Sr p, ∃ s : ℕ,
      (∃ f : Fin s → Fin (p.k + 1), ∑ j, (p.w - p.r (f j)) = a) ∧
      (s : ℤ) * p.w ≤ a + ((b.c + p.w) / d p) * p.w) := by
  sorry

theorem saturation (p : Data) (b : Conductor p) (y : Point)
    (hy : y ∈ star p) (hsize : s0 p b * p.w ≤ y.1 + y.2) : y ∈ T p := by
  sorry

-- PROOF.md 67-75.
theorem strip_membership (p : Data) (b : Conductor p) (l : ℤ) (hl : 0 ≤ l)
    (hsize : max b.c (s0 p b * p.w) ≤ d p * m p l) (y : Point)
    (hy : y ∈ strip p l) :
    chi p l y ↔ y ∈ T p ∨ y.2 - d p * M p l ∈ Sr p := by
  sorry

-- PROOF.md 81-85. L is the least nonnegative integer meeting the bound.
def cbar (p : Data) (b : Conductor p) : ℤ := b.c + s0 p b * p.w
def D (p : Data) (b : Conductor p) : ℤ := cbar p b + p.w
def K (p : Data) (b : Conductor p) : ℤ := cbar p b + D p b
def L (p : Data) (b : Conductor p) : ℤ :=
  max 0 ((6 * K p b - d p * p.n + d p * p.w - 1) / (d p * p.w))

theorem constants (p : Data) (b : Conductor p) :
    0 < p.w ∧ p.w ≤ cbar p b ∧ b.c ≤ cbar p b ∧
    s0 p b * p.w ≤ cbar p b ∧ D p b ≤ K p b ∧
    0 ≤ L p b ∧
    (∀ l : ℤ, L p b ≤ l ↔ 0 ≤ l ∧ 6 * K p b ≤ d p * m p l) := by
  sorry

-- PROOF.md 87.
theorem far_in_T (p : Data) (b : Conductor p) (y : Point) (hy : y ∈ lattice p)
    (h : (cbar p b ≤ y.1 ∧ y.2 ∈ Sr p) ∨ (y.1 ∈ S p ∧ cbar p b ≤ y.2)) :
    y ∈ T p := by
  sorry

-- PROOF.md 89-104.
theorem rule_D (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p)
    (h : (cbar p b ≤ y.1 ∧ cbar p b ≤ y.2) ∨
      (cbar p b - d p * m p l ≤ y.1 ∧ d p * M p l + cbar p b ≤ y.2)) :
    chi p l y := by
  sorry

theorem rule_N (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p)
    (ha : -d p * m p l ≤ y.1 ∧ y.1 < d p * m p l) (hb : y.2 < 0) :
    ¬ chi p l y := by
  sorry

theorem rule_O (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p) (hbox : |y.1| ≤ 2 * K p b ∧ |y.2| ≤ 2 * K p b) :
    chi p l y ↔ y ∈ T p := by
  sorry

theorem rule_P (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (z : Point) (hz : z ∈ coset p) (hbox : |z.1| ≤ 2 * K p b ∧ |z.2| ≤ 2 * K p b) :
    chi p l (P p l + z) ↔ z.1 ∈ S p ∨ z.2 ∈ Sr p := by
  sorry

theorem rule_bottom (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p)
    (ha : cbar p b ≤ y.1 ∧ y.1 < d p * m p l) (hb : |y.2| ≤ 2 * K p b) :
    chi p l y ↔ y.2 ∈ Sr p := by
  sorry

theorem rule_left (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p)
    (ha : |y.1| ≤ 2 * K p b) (hb : cbar p b ≤ y.2 ∧ y.2 < d p * M p l) :
    chi p l y ↔ y.1 ∈ S p := by
  sorry

-- PROOF.md 110-142.
def phiO (p : Data) (b : Conductor p) : Set Point :=
  {e | e ∈ lattice p ∧ (0 ≤ e.1 ∧ e.1 < cbar p b) ∧
    (0 ≤ e.2 ∧ e.2 < cbar p b) ∧ e ∉ T p ∧ ∀ i, e + g p i ∈ T p}
def phiP (p : Data) (b : Conductor p) : Set Point :=
  {z | z ∈ coset p ∧ (-p.w ≤ z.1 ∧ z.1 < b.c) ∧
    (-p.w ≤ z.2 ∧ z.2 < b.c) ∧ z.1 ∉ S p ∧ z.2 ∉ Sr p ∧
    ∀ i, z.1 + p.r i ∈ S p ∨ z.2 + p.w - p.r i ∈ Sr p}
def pfLifts (p : Data) (b : Conductor p) (l : ℤ) : Set Point :=
  phiO p b ∪ Set.image (fun z => P p l + z) (phiP p b)

theorem phiO_finite (p : Data) (b : Conductor p) :
    (phiO p b).Finite := by
  sorry

theorem pf_bijection (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (phiP p b).Finite ∧
    Set.BijOn (proj p l) (pfLifts p b l) (pseudoFrobenius (H p l)) := by
  sorry

-- PROOF.md 292-294; permits omitting the vacuous branch in Lemma 7.
theorem phiP_nonempty (p : Data) (b : Conductor p) : (phiP p b).Nonempty := by
  sorry

-- PROOF.md 149-166. The three arguments represent the three profile arrays.
def differences (U V : Set Point) : Set Point := {z | ∃ u ∈ U, ∃ v ∈ V, z = u - v}
def delta0 (p : Data) (b : Conductor p) : Set Point :=
  differences (phiO p b) (phiO p b) ∪ differences (phiP p b) (phiP p b)
def deltaPlus (p : Data) (b : Conductor p) : Set Point := differences (phiP p b) (phiO p b)
def deltaMinus (p : Data) (b : Conductor p) : Set Point := differences (phiO p b) (phiP p b)

theorem difference_bounds (p : Data) (b : Conductor p) :
    (∀ z ∈ delta0 p b, z ∈ lattice p) ∧
    (∀ z ∈ deltaPlus p b, z ∈ coset p) ∧
    (∀ z ∈ deltaMinus p b, -z ∈ coset p) ∧
    ∀ z ∈ delta0 p b ∪ deltaPlus p b ∪ deltaMinus p b,
      |z.1| < D p b ∧ |z.2| < D p b := by
  sorry

def eval (p : Data) (b : Conductor p) (q0 qp qm : Point → Prop) : Prop :=
  (∃ u ∈ phiP p b, (∀ f ∈ phiP p b, q0 (u - f)) ∧
    (∀ e ∈ phiO p b, qp (u - e))) ∨
  (∃ e ∈ phiO p b, (∀ e2 ∈ phiO p b, q0 (e - e2)) ∧
    (∀ f ∈ phiP p b, qm (e - f)))
def tau (p : Data) (b : Conductor p) (l : ℤ) (y : Point) : Prop :=
  eval p b (fun z => chi p l (y + z))
    (fun z => chi p l (y + P p l + z)) (fun z => chi p l (y - P p l + z))

theorem trace_criterion (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (∀ y ∈ lattice p, proj p l y ∈ trace (H p l) ↔ chi p l y ∧ tau p b l y) ∧
    (∀ y ∈ lattice p, ∀ j : ℤ, tau p b l (y + j • v p l) ↔ tau p b l y) := by
  sorry

-- PROOF.md 195-232: explicit fixed predicates, not existential choices.
def beta (p : Data) (b : Conductor p) (a : ℤ) : Prop :=
  eval p b (fun z => a + z.2 ∈ Sr p) (fun _ => True) (fun _ => False)
def alpha (p : Data) (b : Conductor p) (a : ℤ) : Prop :=
  eval p b (fun z => a + z.1 ∈ S p) (fun _ => True) (fun _ => False)
def thetaO (p : Data) (b : Conductor p) (y : Point) : Prop :=
  eval p b (fun z => y + z ∈ T p)
    (fun z => y.1 + z.1 ∈ S p ∨ y.2 + z.2 ∈ Sr p) (fun _ => False)
def thetaP (p : Data) (b : Conductor p) (y : Point) : Prop :=
  eval p b (fun z => y.1 + z.1 ∈ S p ∨ y.2 + z.2 ∈ Sr p)
    (fun _ => True) (fun z => y + z ∈ T p)

-- PROOF.md 172-178, 213-215.
def regionO (p : Data) (b : Conductor p) : Set Point :=
  {y | y ∈ lattice p ∧ (0 ≤ y.1 ∧ y.1 < K p b) ∧ (0 ≤ y.2 ∧ y.2 < K p b)}
def regionBottom (p : Data) (b : Conductor p) (l : ℤ) : Set Point :=
  {y | y ∈ positiveStrip p l ∧ K p b ≤ y.1 ∧ y.1 < d p * m p l - K p b ∧ y.2 < K p b}
def regionLeft (p : Data) (b : Conductor p) (l : ℤ) : Set Point :=
  {y | y ∈ positiveStrip p l ∧ y.1 < K p b ∧ K p b ≤ y.2 ∧ y.2 < d p * M p l - K p b}
def regionP (p : Data) (b : Conductor p) (l : ℤ) : Set Point :=
  {y | y ∈ positiveStrip p l ∧
    ((d p * m p l - K p b ≤ y.1 ∧ y.2 < K p b) ∨
     (y.1 < K p b ∧ d p * M p l - K p b ≤ y.2 ∧ y.2 ≤ d p * M p l + K p b))}
def regionDeep (p : Data) (b : Conductor p) (l : ℤ) : Set Point :=
  {y | y ∈ positiveStrip p l ∧
    ((K p b ≤ y.1 ∧ K p b ≤ y.2) ∨ (y.1 < K p b ∧ d p * M p l + K p b < y.2))}
def ZP (p : Data) (b : Conductor p) : Set Point :=
  {z | z ∈ coset p ∧
    (((-K p b ≤ z.1 ∧ z.1 < 0) ∧ (0 ≤ z.2 ∧ z.2 < K p b)) ∨
     ((0 ≤ z.1 ∧ z.1 < K p b) ∧ (-K p b ≤ z.2 ∧ z.2 ≤ K p b)))}
def cornerMap (p : Data) (l : ℤ) (z : Point) : Point :=
  if z.1 < 0 then (z.1 + d p * m p l, z.2) else P p l + z
def regions (p : Data) (b : Conductor p) (l : ℤ) : Fin 5 → Set Point :=
  ![regionO p b, regionBottom p b l, regionLeft p b l, regionP p b l, regionDeep p b l]

theorem region_partition (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (⋃ i, regions p b l i) = positiveStrip p l ∧
    Pairwise (fun i j : Fin 5 => Disjoint (regions p b l i) (regions p b l j)) := by
  sorry

-- PROOF.md 183-232.
theorem deep_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ regionDeep p b l) : chi p l y ∧ tau p b l y := by
  sorry

theorem bottom_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ regionBottom p b l) :
    (chi p l y ↔ y.2 ∈ Sr p) ∧ (tau p b l y ↔ beta p b y.2) := by
  sorry

theorem left_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ regionLeft p b l) :
    (chi p l y ↔ y.1 ∈ S p) ∧ (tau p b l y ↔ alpha p b y.1) := by
  sorry

theorem origin_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ regionO p b) :
    (chi p l y ↔ y ∈ T p) ∧ (tau p b l y ↔ thetaO p b y) := by
  sorry

theorem corner_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    Set.BijOn (cornerMap p l) (ZP p b) (regionP p b l) ∧
    ∀ z ∈ ZP p b,
      (chi p l (cornerMap p l z) ↔ z.1 ∈ S p ∨ z.2 ∈ Sr p) ∧
      (tau p b l (cornerMap p l z) ↔ thetaP p b z) := by
  sorry

-- PROOF.md 180-181, 243, 250-257.
def badLifts (p : Data) (b : Conductor p) (l : ℤ) : Set Point :=
  {y | y ∈ positiveStrip p l ∧ chi p l y ∧ ¬ tau p b l y}
def badA (p : Data) (b : Conductor p) : Set ℤ :=
  {a | d p ∣ a ∧ 0 ≤ a ∧ a < K p b ∧ a ∈ S p ∧ ¬ alpha p b a}
def badB (p : Data) (b : Conductor p) : Set ℤ :=
  {a | d p ∣ a ∧ 0 ≤ a ∧ a < K p b ∧ a ∈ Sr p ∧ ¬ beta p b a}
def badO (p : Data) (b : Conductor p) : Set Point :=
  {y | y ∈ regionO p b ∧ y ∈ T p ∧ ¬ thetaO p b y}
def badP (p : Data) (b : Conductor p) : Set Point :=
  {z | z ∈ ZP p b ∧ (z.1 ∈ S p ∨ z.2 ∈ Sr p) ∧ ¬ thetaP p b z}
def interval (w X Y rho : ℤ) : Set ℤ := {x | X ≤ x ∧ x < Y ∧ x % w = rho % w}
noncomputable def intervalCount (w X Y rho : ℤ) : ℕ := (interval w X Y rho).ncard

theorem bad_finite (p : Data) (b : Conductor p) :
    (badA p b).Finite ∧ (badB p b).Finite ∧ (badO p b).Finite ∧ (badP p b).Finite := by
  sorry

theorem bad_lifts_bijection (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (badLifts p b l).Finite ∧
    Set.BijOn (proj p l) (badLifts p b l) (H p l \ trace (H p l)) := by
  sorry

-- PROOF.md 238-240, 259. General nonnegative block count, including zero.
theorem interval_count_add (w X Y rho t : ℤ) (hw : 0 < w) (ht : 0 ≤ t) (hXY : X ≤ Y) :
    (interval w X Y rho).Finite ∧
    (intervalCount w X (Y + t * w) rho : ℤ) =
      (intervalCount w X Y rho : ℤ) + t := by
  sorry

noncomputable def total (p : Data) (b : Conductor p) (l : ℤ) : ℕ :=
  (badO p b).ncard + (badP p b).ncard +
    ∑ a ∈ (bad_finite p b).2.1.toFinset, intervalCount p.w (K p b) (d p * m p l - K p b) (-a) +
    ∑ a ∈ (bad_finite p b).1.toFinset, intervalCount p.w (K p b) (d p * M p l - K p b) (-a)

-- PROOF.md 247-262; in particular this proves finiteness of the residue.
theorem residue_count (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    traceResidue (H p l) = (total p b l : ℕ∞) := by
  sorry

noncomputable def slope (p : Data) (b : Conductor p) : ℤ :=
  d p * ((badA p b).ncard + (badB p b).ncard : ℕ)

theorem count_affine (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (total p b l : ℤ) = (total p b (L p b) : ℤ) + slope p b * (l - L p b) := by
  sorry

theorem explicit_affine (p : Data) (b : Conductor p) :
    0 ≤ slope p b ∧ 0 ≤ L p b ∧ ∀ l : ℤ, L p b ≤ l →
      ∃ N : ℕ, traceResidue (H p l) = N ∧
        (N : ℤ) = slope p b * l + ((total p b (L p b) : ℤ) - slope p b * L p b) := by
  sorry

-- PROOF.md 281-283: proved corollaries, not additional records.
theorem eventual_type (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (pseudoFrobenius (H p l)).Finite ∧
    (pseudoFrobenius (H p l)).ncard = (phiO p b).ncard + (phiP p b).ncard := by
  sorry

theorem trace_add (Q : AddSubmonoid ℤ) (h t : ℤ)
    (hh : h ∈ trace (Q : Set ℤ)) (ht : t ∈ Q) :
    h + t ∈ trace (Q : Set ℤ) := by
  sorry

theorem nearly_gorenstein (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (∀ h ∈ H p l, h ≠ 0 → h ∈ trace (H p l)) ↔
      ∀ i, thetaO p b (g p i) := by
  sorry

theorem constant_iff (p : Data) (b : Conductor p) :
    (∃ C : ℕ, ∀ l : ℤ, L p b ≤ l → traceResidue (H p l) = C) ↔
      badA p b = ∅ ∧ badB p b = ∅ := by
  sorry

end Plan

-- PROOF.md 242-264. Signature copied character for character from Challenge.lean.
theorem trace_residue_eventually_affine_dev (k : ℕ) (hk : 2 ≤ k) (r : Fin (k + 1) → ℤ) (w n : ℤ) (hr0 : r 0 = 0) (hr : StrictMono r) (hw : r (Fin.last k) = w) (hn : 0 < n) (hnd : Int.gcd n (Finset.univ.gcd fun i : Fin k => r i.succ) = 1) : ∃ A B L : ℤ, 0 ≤ A ∧ 0 ≤ L ∧ ∀ l : ℤ, L ≤ l → ∃ N : ℕ, traceResidue (shiftedSemigroup k r n w l : Set ℤ) = N ∧ (N : ℤ) = A * l + B := by
  sorry

end EventualAffineTraceResidue
