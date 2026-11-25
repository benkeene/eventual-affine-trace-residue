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
private theorem base_idx_last (p : Data) :
    (⟨p.k - 1, by have := p.hk; omega⟩ : Fin p.k).succ = Fin.last p.k := by
  ext; simp; have := p.hk; omega

theorem arithmetic (p : Data) :
    0 < d p ∧ 0 < p.w ∧ d p ∣ p.w ∧
    (∀ i, 0 ≤ p.r i ∧ p.r i ≤ p.w ∧ d p ∣ p.r i) ∧
    ∀ l : ℤ, 0 ≤ l → 0 < m p l ∧ Int.gcd (m p l) (d p) = 1 := by
  have hdw : d p ∣ p.w := by
    have : d p ∣ p.r (Fin.succ (⟨p.k - 1, by have := p.hk; omega⟩ : Fin p.k)) :=
      Finset.gcd_dvd (f := fun i : Fin p.k => p.r i.succ) (Finset.mem_univ _)
    rwa [base_idx_last, p.hw] at this
  have hw : 0 < p.w := by
    rw [← p.hw, ← p.hr0]
    apply p.hr
    rw [Fin.lt_def]; simp; have := p.hk; omega
  have hd0 : 0 ≤ d p := Finset.Int.finsetGcd_nonneg
  have hd : 0 < d p := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hdw; simp at hdw; omega
  refine ⟨hd, hw, hdw, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · rw [← p.hr0]; exact p.hr.monotone (Fin.zero_le i)
    · rw [← p.hw]; exact p.hr.monotone (Fin.le_last i)
    · refine Fin.cases ?_ (fun j => ?_) i
      · rw [p.hr0]; exact dvd_zero _
      · exact Finset.gcd_dvd (f := fun i : Fin p.k => p.r i.succ) (Finset.mem_univ j)
  · intro l hl
    refine ⟨?_, ?_⟩
    · unfold m; have := p.hn; positivity
    · unfold m
      rw [Int.gcd_add_right_left_of_dvd p.n (Dvd.dvd.mul_left hdw l)]
      exact p.hnd

-- PROOF.md 18; the conductor is arbitrary, not necessarily least.
structure Conductor (p : Data) where
  c : ℤ
  nonneg : 0 ≤ c
  dvd : d p ∣ c
  covers : ∀ x : ℤ, d p ∣ x → c ≤ x → x ∈ S p ∧ x ∈ Sr p

private theorem base_gcd_mem (ι : Type) (s : Finset ι) (f : ι → ℤ) :
    s.gcd f ∈ AddSubgroup.closure (Set.range f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.gcd_insert, ← Int.coe_gcd, Int.gcd_eq_gcd_ab]
    refine AddSubgroup.add_mem _ ?_ ?_
    · rw [mul_comm, ← smul_eq_mul]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self a)) _
    · rw [mul_comm, ← smul_eq_mul]
      exact AddSubgroup.zsmul_mem _ ih _

private theorem base_sub_of_closure (ι : Type) (G : ι → ℤ) (x : ℤ)
    (hx : x ∈ AddSubgroup.closure (Set.range G)) :
    ∃ A ∈ AddSubmonoid.closure (Set.range G), ∃ B ∈ AddSubmonoid.closure (Set.range G),
      x = A - B := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => exact ⟨x, AddSubmonoid.subset_closure hx, 0, AddSubmonoid.zero_mem _, by simp⟩
  | zero => exact ⟨0, AddSubmonoid.zero_mem _, 0, AddSubmonoid.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, B, hB, rfl⟩ := hx
    obtain ⟨A', hA', B', hB', rfl⟩ := hy
    exact ⟨A + A', AddSubmonoid.add_mem _ hA hA', B + B', AddSubmonoid.add_mem _ hB hB', by ring⟩
  | neg x _ hx =>
    obtain ⟨A, hA, B, hB, rfl⟩ := hx
    exact ⟨B, hB, A, hA, by ring⟩

private theorem base_cofinite (Q : AddSubmonoid ℤ) (e : ℤ) (he : 0 < e)
    (hQ : ∀ q ∈ Q, 0 ≤ q ∧ e ∣ q) (A B : ℤ) (hA : A ∈ Q) (hB : B ∈ Q) (hAB : A = B + e) :
    ∃ c : ℤ, 0 ≤ c ∧ e ∣ c ∧ ∀ x : ℤ, e ∣ x → c ≤ x → x ∈ Q := by
  obtain ⟨hB0, t, rfl⟩ := hQ B hB
  have ht : 0 ≤ t := by nlinarith
  rcases ht.lt_or_eq with ht | ht
  · refine ⟨e * t * t, by positivity, ⟨t * t, by ring⟩, ?_⟩
    rintro x ⟨y, rfl⟩ hx
    have hy : t * t ≤ y := by nlinarith
    have hq : t ≤ y / t := by
      rw [Int.le_ediv_iff_mul_le ht]; linarith
    have hρ0 : 0 ≤ y % t := Int.emod_nonneg _ ht.ne'
    have hρ : y % t < t := Int.emod_lt_of_pos _ ht
    have hdecomp := Int.mul_ediv_add_emod y t
    have key : e * y = (y / t - y % t).toNat • (e * t) + (y % t).toNat • A := by
      rw [nsmul_eq_mul, nsmul_eq_mul, Int.toNat_of_nonneg (by linarith),
        Int.toNat_of_nonneg hρ0, hAB]
      linear_combination (-e) * hdecomp
    rw [key]
    exact Q.add_mem (Q.nsmul_mem hB _) (Q.nsmul_mem hA _)
  · subst ht
    refine ⟨0, le_refl _, dvd_zero _, ?_⟩
    rintro x ⟨y, rfl⟩ hx
    have hy : 0 ≤ y := by nlinarith
    have key : e * y = y.toNat • A := by
      rw [nsmul_eq_mul, Int.toNat_of_nonneg hy, hAB]; ring
    rw [key]; exact Q.nsmul_mem hA _

private theorem base_d_mem (p : Data) : d p ∈ AddSubgroup.closure (Set.range p.r) := by
  have h := base_gcd_mem (Fin p.k) Finset.univ (fun i : Fin p.k => p.r i.succ)
  refine AddSubgroup.closure_mono ?_ h
  rintro _ ⟨i, rfl⟩; exact ⟨i.succ, rfl⟩

private theorem base_S_nonneg (p : Data) : ∀ a ∈ S p, 0 ≤ a ∧ d p ∣ a := by
  intro a ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨((arithmetic p).2.2.2.1 i).1, ((arithmetic p).2.2.2.1 i).2.2⟩
  | zero => exact ⟨le_refl _, dvd_zero _⟩
  | add x y _ _ hx hy => exact ⟨add_nonneg hx.1 hy.1, dvd_add hx.2 hy.2⟩

private theorem base_Sr_nonneg (p : Data) : ∀ a ∈ Sr p, 0 ≤ a ∧ d p ∣ a := by
  intro a ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have h := (arithmetic p).2.2.2.1 i
    exact ⟨by linarith [h.2.1], dvd_sub (arithmetic p).2.2.1 h.2.2⟩
  | zero => exact ⟨le_refl _, dvd_zero _⟩
  | add x y _ _ hx hy => exact ⟨add_nonneg hx.1 hy.1, dvd_add hx.2 hy.2⟩

theorem conductor_exists (p : Data) : Nonempty (Conductor p) := by
  have hA := arithmetic p
  -- S
  obtain ⟨A, hA1, B, hB1, hAB1⟩ := base_sub_of_closure _ _ _ (base_d_mem p)
  obtain ⟨c1, hc1, hdc1, hcov1⟩ :=
    base_cofinite (S p) (d p) hA.1 (base_S_nonneg p) A B hA1 hB1 (by linarith)
  -- Sr
  have hmem : d p ∈ AddSubgroup.closure (Set.range fun i => p.w - p.r i) := by
    refine (AddSubgroup.closure_le _).2 ?_ (base_d_mem p)
    rintro _ ⟨i, rfl⟩
    have h0 : p.r i = (p.w - p.r 0) - (p.w - p.r i) := by rw [p.hr0]; ring
    rw [h0]
    exact AddSubgroup.sub_mem _
      (AddSubgroup.subset_closure (Set.mem_range_self (f := fun i => p.w - p.r i) 0))
      (AddSubgroup.subset_closure (Set.mem_range_self (f := fun i => p.w - p.r i) i))
  obtain ⟨A', hA2, B', hB2, hAB2⟩ := base_sub_of_closure _ _ _ hmem
  obtain ⟨c2, hc2, hdc2, hcov2⟩ :=
    base_cofinite (Sr p) (d p) hA.1 (base_Sr_nonneg p) A' B' hA2 hB2 (by linarith)
  exact ⟨⟨max c1 c2, le_max_of_le_left hc1, by
    rcases le_total c1 c2 with h | h
    · rw [max_eq_right h]; exact hdc2
    · rw [max_eq_left h]; exact hdc1,
    fun x hx hcx => ⟨hcov1 x hx (le_of_max_le_left hcx), hcov2 x hx (le_of_max_le_right hcx)⟩⟩⟩

-- PROOF.md 44, 49, 53.
private theorem base_sum_append (ι : Type) (G : ι → ℤ) (s t : ℕ) (f : Fin s → ι)
    (g : Fin t → ι) : ∑ j, G (Fin.append f g j) = ∑ j, G (f j) + ∑ j, G (g j) := by
  rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

private theorem base_sum_g (p : Data) (s : ℕ) (f : Fin s → Fin (p.k + 1)) :
    ∑ j, g p (f j) = (∑ j, p.r (f j), (s : ℤ) * p.w - ∑ j, p.r (f j)) := by
  ext
  · simp [g, Prod.fst_sum]
  · simp [g, Prod.snd_sum, Finset.sum_sub_distrib]

theorem monoid_model (p : Data) :
    (∀ y : Point, y ∈ T p ↔ ∃ s : ℕ, y.1 ∈ sums p s ∧ y.2 = s * p.w - y.1) ∧
    (∀ y ∈ T p, y ∈ star p) ∧
    (∀ a ∈ S p, 0 ≤ a ∧ d p ∣ a) ∧
    (∀ b ∈ Sr p, 0 ≤ b ∧ d p ∣ b) := by
  have hA := arithmetic p
  refine ⟨fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun y hy => ?_, base_S_nonneg p, base_Sr_nonneg p⟩
  · induction hy using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨1, ⟨fun _ => i, by simp [g]⟩, by simp [g]⟩
    | zero => exact ⟨0, ⟨Fin.elim0, by simp⟩, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, ⟨f, hf⟩, hs⟩ := hx
      obtain ⟨t, ⟨f', hf'⟩, ht⟩ := hy
      refine ⟨s + t, ⟨Fin.append f f', ?_⟩, ?_⟩
      · rw [base_sum_append, hf, hf']; rfl
      · simp only [Prod.fst_add, Prod.snd_add, hs, ht]; push_cast; ring
  · obtain ⟨s, ⟨f, hf⟩, hs⟩ := hy
    have : y = ∑ j, g p (f j) := by
      rw [base_sum_g, hf]; ext <;> simp [hs]
    rw [this]
    exact AddSubmonoid.sum_mem _ (fun j _ => AddSubmonoid.subset_closure ⟨f j, rfl⟩)
  · induction hy using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have h := hA.2.2.2.1 i
      refine ⟨⟨h.2.2, dvd_sub hA.2.2.1 h.2.2, by simp [g]⟩,
        AddSubmonoid.subset_closure ⟨i, rfl⟩, AddSubmonoid.subset_closure ⟨i, rfl⟩⟩
    | zero => exact ⟨⟨dvd_zero _, dvd_zero _, by simp⟩, AddSubmonoid.zero_mem _,
        AddSubmonoid.zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hx
      obtain ⟨⟨h1', h2', h3'⟩, h4', h5'⟩ := hy
      refine ⟨⟨dvd_add h1 h1', dvd_add h2 h2', ?_⟩, AddSubmonoid.add_mem _ h4 h4',
        AddSubmonoid.add_mem _ h5 h5'⟩
      have := dvd_add h3 h3'
      simp only [Prod.fst_add, Prod.snd_add]
      convert this using 1; ring

-- PROOF.md 36-46, 24. No additivity is asserted off the lattice.
private theorem base_proj_of (p : Data) (l : ℤ) (y : Point) (s : ℤ)
    (h : y.1 + y.2 = p.w * s) : proj p l y = y.1 + s * m p l := by
  have hw := (arithmetic p).2.1
  unfold proj
  have : y.1 * M p l + y.2 * m p l = p.w * (y.1 + s * m p l) := by
    have h2 : y.2 = p.w * s - y.1 := by linarith
    rw [h2]; unfold M; ring
  rw [this, Int.mul_ediv_cancel_left _ hw.ne']

private theorem base_proj_add_smul_v (p : Data) (l : ℤ) (y : Point) (j : ℤ) :
    proj p l (y + j • v p l) = proj p l y := by
  unfold proj
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, v, M]
  ring

private theorem base_proj_add (p : Data) (l : ℤ) (x y : Point) (hx : x ∈ lattice p)
    (hy : y ∈ lattice p) : proj p l (x + y) = proj p l x + proj p l y := by
  obtain ⟨s, hs⟩ := hx.2.2
  obtain ⟨t, ht⟩ := hy.2.2
  rw [base_proj_of p l x s hs, base_proj_of p l y t ht,
    base_proj_of p l (x + y) (s + t) (by simp only [Prod.fst_add, Prod.snd_add]; linarith)]
  simp only [Prod.fst_add]; ring

private theorem base_lat_add (p : Data) (x y : Point) (hx : x ∈ lattice p)
    (hy : y ∈ lattice p) : x + y ∈ lattice p := by
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨h1', h2', h3'⟩ := hy
  refine ⟨dvd_add h1 h1', dvd_add h2 h2', ?_⟩
  have := dvd_add h3 h3'
  simp only [Prod.fst_add, Prod.snd_add]
  convert this using 1; ring

private theorem base_lat_neg (p : Data) (x : Point) (hx : x ∈ lattice p) :
    -x ∈ lattice p := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨(dvd_neg).2 h1, (dvd_neg).2 h2, ?_⟩
  have := (dvd_neg).2 h3
  simp only [Prod.fst_neg, Prod.snd_neg]
  convert this using 1; ring

private theorem base_lat_sub (p : Data) (x y : Point) (hx : x ∈ lattice p)
    (hy : y ∈ lattice p) : x - y ∈ lattice p := by
  rw [sub_eq_add_neg]; exact base_lat_add p x (-y) hx (base_lat_neg p y hy)

private theorem base_v_mem (p : Data) (l : ℤ) (j : ℤ) : j • v p l ∈ lattice p := by
  have hA := arithmetic p
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul, v]; exact ⟨-(j * m p l), by ring⟩
  · simp only [Prod.smul_snd, smul_eq_mul, v]; exact ⟨j * M p l, by ring⟩
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, v, M]
    exact ⟨j * d p, by ring⟩

private theorem base_kernel (p : Data) (l : ℤ) (hl : 0 ≤ l) (y : Point) (hy : y ∈ lattice p) :
    proj p l y = 0 ↔ ∃ j : ℤ, y = j • v p l := by
  have hA := arithmetic p
  constructor
  · intro h0
    obtain ⟨s, hs⟩ := hy.2.2
    rw [base_proj_of p l y s hs] at h0
    have hds : d p ∣ s * m p l := by
      have : s * m p l = -y.1 := by linarith
      rw [this]; exact (dvd_neg).2 hy.1
    have hgcd : Int.gcd (d p) (m p l) = 1 := by
      rw [Int.gcd_comm]; exact ((hA.2.2.2.2 l hl).2)
    obtain ⟨j, hj⟩ := Int.dvd_of_dvd_mul_left_of_gcd_one hds hgcd
    refine ⟨j, ?_⟩
    ext
    · simp only [Prod.smul_fst, smul_eq_mul, v]; rw [hj] at h0; linarith
    · simp only [Prod.smul_snd, smul_eq_mul, v, M]; rw [hj] at h0 hs; linarith
  · rintro ⟨j, rfl⟩
    have := base_proj_add_smul_v p l 0 j
    rw [zero_add] at this
    rw [this]
    unfold proj; simp

theorem lattice_model (p : Data) (l : ℤ) (hl : 0 ≤ l) :
    (∀ x ∈ lattice p, ∀ y ∈ lattice p, proj p l (x + y) = proj p l x + proj p l y) ∧
    (∀ x : ℤ, ∃ y ∈ lattice p, proj p l y = x) ∧
    (∀ y ∈ lattice p, proj p l y = 0 ↔ ∃ j : ℤ, y = j • v p l) ∧
    (∀ i, proj p l (g p i) = m p l + p.r i) ∧
    H p l = Set.image (proj p l) (T p : Set Point) ∧
    (∀ z : Point, z ∈ coset p ↔ P p l + z ∈ lattice p) := by
  have hA := arithmetic p
  have hg : ∀ i, proj p l (g p i) = m p l + p.r i := by
    intro i
    rw [base_proj_of p l (g p i) 1 (by simp [g])]; simp [g]; ring
  have hTl : ∀ y ∈ T p, y ∈ lattice p := fun y hy => ((monoid_model p).2.1 y hy).1
  refine ⟨fun x hx y hy => base_proj_add p l x y hx hy, ?_, base_kernel p l hl, hg, ?_, ?_⟩
  · intro x
    have h1 := Int.gcd_eq_gcd_ab (m p l) (d p)
    rw [(hA.2.2.2.2 l hl).2] at h1
    refine ⟨(d p * (x * Int.gcdB (m p l) (d p)),
      p.w * (x * Int.gcdA (m p l) (d p)) - d p * (x * Int.gcdB (m p l) (d p))), ?_, ?_⟩
    · exact ⟨dvd_mul_right _ _, dvd_sub (Dvd.dvd.mul_right hA.2.2.1 _) (dvd_mul_right _ _),
        ⟨x * Int.gcdA (m p l) (d p), by ring⟩⟩
    · rw [base_proj_of p l _ (x * Int.gcdA (m p l) (d p)) (by ring)]
      linear_combination x * h1.symm
  · apply Set.Subset.antisymm
    · intro x hx
      induction hx using AddSubmonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨g p i, AddSubmonoid.subset_closure ⟨i, rfl⟩, hg i⟩
      | zero => exact ⟨0, AddSubmonoid.zero_mem _, by unfold proj; simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨t, ht, rfl⟩ := hx
        obtain ⟨t', ht', rfl⟩ := hy
        exact ⟨t + t', AddSubmonoid.add_mem _ ht ht',
          base_proj_add p l t t' (hTl t ht) (hTl t' ht')⟩
    · rintro _ ⟨t, ht, rfl⟩
      induction ht using AddSubmonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [hg i]
        exact AddSubmonoid.subset_closure ⟨i, rfl⟩
      | zero =>
        have : proj p l 0 = 0 := by unfold proj; simp
        rw [this]; exact AddSubmonoid.zero_mem _
      | add x y hx' hy' hx hy =>
        rw [base_proj_add p l x y (hTl x hx') (hTl y hy')]
        exact AddSubmonoid.add_mem _ hx hy
  · intro z
    unfold coset lattice P
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, zero_add]
    have e1 : z.1 + (d p * M p l + z.2) = (z.1 + z.2 + d p * p.n) + p.w * (d p * (l + 1)) := by
      unfold M m; ring
    rw [e1, dvd_add_left (dvd_mul_right _ _), dvd_add_right (dvd_mul_right _ _)]

theorem membership_and_lifts (p : Data) (l : ℤ) (hl : 0 ≤ l) :
    (∀ y ∈ lattice p, chi p l y ↔ ∃ j : ℤ, y + j • v p l ∈ T p) ∧
    (∀ y ∈ lattice p, ∀ j : ℤ, chi p l (y + j • v p l) ↔ chi p l y) ∧
    Set.BijOn (proj p l) (strip p l) Set.univ := by
  have hA := arithmetic p
  have hLM := lattice_model p l hl
  have hTl : ∀ y ∈ T p, y ∈ lattice p := fun y hy => ((monoid_model p).2.1 y hy).1
  have hdm : 0 < d p * m p l := mul_pos hA.1 (hA.2.2.2.2 l hl).1
  refine ⟨fun y hy => ?_, fun y _ j => by unfold chi; rw [base_proj_add_smul_v], ?_, ?_, ?_⟩
  · unfold chi
    rw [hLM.2.2.2.2.1]
    constructor
    · rintro ⟨t, ht, hpt⟩
      have hsub : proj p l (t - y) = 0 := by
        have := base_proj_add p l (t - y) y (base_lat_sub p t y (hTl t ht) hy) hy
        rw [sub_add_cancel] at this; linarith
      obtain ⟨j, hj⟩ := (base_kernel p l hl _ (base_lat_sub p t y (hTl t ht) hy)).1 hsub
      refine ⟨j, ?_⟩
      have : y + j • v p l = t := by rw [← hj]; abel
      rw [this]; exact ht
    · rintro ⟨j, hj⟩
      exact ⟨_, hj, base_proj_add_smul_v p l y j⟩
  · intro _ _; exact Set.mem_univ _
  · intro x hx y hy hxy
    have hsub : proj p l (x - y) = 0 := by
      have := base_proj_add p l (x - y) y (base_lat_sub p x y hx.1 hy.1) hy.1
      rw [sub_add_cancel] at this; linarith
    obtain ⟨j, hj⟩ := (base_kernel p l hl _ (base_lat_sub p x y hx.1 hy.1)).1 hsub
    have h1 : x.1 - y.1 = j * (-(d p * m p l)) := by
      have := congrArg Prod.fst hj
      simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, v] at this
      rw [this]; ring
    have hj0 : j = 0 := by
      obtain ⟨hx1, hx2⟩ := hx.2
      obtain ⟨hy1, hy2⟩ := hy.2
      rcases lt_trichotomy j 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hj0, zero_smul] at hj
    exact sub_eq_zero.1 hj
  · intro x _
    obtain ⟨y, hy, rfl⟩ := hLM.2.1 x
    refine ⟨y + (y.1 / (d p * m p l)) • v p l, ⟨base_lat_add p _ _ hy (base_v_mem p l _), ?_, ?_⟩,
      base_proj_add_smul_v p l y _⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, v]
      have := Int.emod_nonneg y.1 hdm.ne'
      rw [Int.emod_def] at this; linarith
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, v]
      have := Int.emod_lt_of_pos y.1 hdm
      rw [Int.emod_def] at this; linarith

-- PROOF.md 28, 37, 44, 148.
private theorem base_H_nonneg (p : Data) (l : ℤ) (hl : 0 ≤ l) : ∀ h ∈ H p l, 0 ≤ h := by
  have hA := arithmetic p
  intro h hh
  induction hh using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have := (hA.2.2.2.2 l hl).1; have := (hA.2.2.2.1 i).1
    unfold m at *; linarith
  | zero => exact le_refl _
  | add x y _ _ hx hy => exact add_nonneg hx hy

private theorem base_H_decomp (p : Data) (l : ℤ) (h : ℤ) (hh : h ∈ H p l) :
    h = 0 ∨ ∃ i, ∃ h' ∈ H p l, h = m p l + p.r i + h' := by
  induction hh using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Or.inr ⟨i, 0, AddSubmonoid.zero_mem _, by unfold m; ring⟩
  | zero => exact Or.inl rfl
  | add x y hx' hy' hx hy =>
    rcases hx with rfl | ⟨i, h', hh', rfl⟩
    · rw [zero_add]; exact hy
    · exact Or.inr ⟨i, h' + y, AddSubmonoid.add_mem _ hh' hy', by ring⟩

theorem numerical_and_pf_test (p : Data) (l : ℤ) (hl : 0 ≤ l) :
    (∀ h ∈ H p l, 0 ≤ h) ∧
    (∃ C : ℤ, ∀ h : ℤ, C ≤ h → h ∈ H p l) ∧
    (∀ x : ℤ, x ∈ pseudoFrobenius (H p l) ↔
      x ∉ H p l ∧ ∀ i, x + m p l + p.r i ∈ H p l) := by
  have hA := arithmetic p
  have hgen : ∀ i, m p l + p.r i ∈ H p l := fun i => AddSubmonoid.subset_closure ⟨i, rfl⟩
  have hgpos : ∀ i, 0 < m p l + p.r i := by
    intro i; have := (hA.2.2.2.2 l hl).1; have := (hA.2.2.2.1 i).1; linarith
  refine ⟨base_H_nonneg p l hl, ?_, ?_⟩
  · -- 1 is an integer combination of the generators
    have hsub : AddSubgroup.closure (Set.range p.r) ≤
        AddSubgroup.closure (Set.range fun i => p.n + l * p.w + p.r i) := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      have : p.r i = (p.n + l * p.w + p.r i) - (p.n + l * p.w + p.r 0) := by rw [p.hr0]; ring
      rw [this]
      exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure ⟨i, rfl⟩)
        (AddSubgroup.subset_closure ⟨0, rfl⟩)
    have hm : m p l ∈ AddSubgroup.closure (Set.range fun i => p.n + l * p.w + p.r i) := by
      have : m p l = p.n + l * p.w + p.r 0 := by rw [p.hr0]; unfold m; ring
      rw [this]; exact AddSubgroup.subset_closure ⟨0, rfl⟩
    have h1 := Int.gcd_eq_gcd_ab (m p l) (d p)
    rw [(hA.2.2.2.2 l hl).2] at h1
    have hone : (1 : ℤ) ∈ AddSubgroup.closure (Set.range fun i => p.n + l * p.w + p.r i) := by
      have : (1 : ℤ) = Int.gcdA (m p l) (d p) • m p l + Int.gcdB (m p l) (d p) • d p := by
        simp only [smul_eq_mul]; linear_combination h1
      rw [this]
      exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hm _)
        (AddSubgroup.zsmul_mem _ (hsub (base_d_mem p)) _)
    obtain ⟨A, hA1, B, hB1, hAB⟩ := base_sub_of_closure _ _ _ hone
    obtain ⟨c, -, -, hc⟩ := base_cofinite (shiftedSemigroup p.k p.r p.n p.w l) 1 one_pos
      (fun q hq => ⟨base_H_nonneg p l hl q hq, one_dvd _⟩) A B hA1 hB1 (by linarith)
    exact ⟨c, fun h hh => hc h (one_dvd _) hh⟩
  · intro x
    constructor
    · rintro ⟨hx, hall⟩
      refine ⟨hx, fun i => ?_⟩
      have := hall _ (hgen i) (hgpos i).ne'
      rwa [← add_assoc] at this
    · rintro ⟨hx, hall⟩
      refine ⟨hx, fun h hh h0 => ?_⟩
      rcases base_H_decomp p l h hh with rfl | ⟨i, h', hh', rfl⟩
      · exact absurd rfl h0
      · have := AddSubmonoid.add_mem _ (hall i) hh'
        rw [show x + (m p l + p.r i + h') = x + m p l + p.r i + h' by ring]
        exact this

-- PROOF.md 50, 55-65. This quotient is exact since d divides c and w.
def s0 (p : Data) (b : Conductor p) : ℤ := 2 * (b.c + p.w) / d p

private theorem base_gen_nonneg (p : Data) (G : Fin (p.k + 1) → ℤ)
    (hG : ∀ i, 0 ≤ G i ∧ d p ∣ G i) :
    ∀ a ∈ AddSubmonoid.closure (Set.range G), 0 ≤ a ∧ d p ∣ a := by
  intro a ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hG i
  | zero => exact ⟨le_refl _, dvd_zero _⟩
  | add x y _ _ hx hy => exact ⟨add_nonneg hx.1 hy.1, dvd_add hx.2 hy.2⟩

private theorem base_short (p : Data) (G : Fin (p.k + 1) → ℤ)
    (hG : ∀ i, 0 ≤ G i ∧ d p ∣ G i) :
    ∀ a ∈ AddSubmonoid.closure (Set.range G), ∃ s : ℕ,
      (∃ f : Fin s → Fin (p.k + 1), ∑ j, G (f j) = a) ∧ (s : ℤ) * d p ≤ a := by
  have hd := (arithmetic p).1
  intro a ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rcases (hG i).1.lt_or_eq with h | h
    · refine ⟨1, ⟨fun _ => i, by simp⟩, ?_⟩
      have := Int.le_of_dvd h (hG i).2
      simpa using this
    · exact ⟨0, ⟨Fin.elim0, by simp [← h]⟩, by simp [← h]⟩
  | zero => exact ⟨0, ⟨Fin.elim0, by simp⟩, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, ⟨f, hf⟩, hs⟩ := hx
    obtain ⟨t, ⟨f', hf'⟩, ht⟩ := hy
    refine ⟨s + t, ⟨Fin.append f f', by rw [base_sum_append, hf, hf']⟩, ?_⟩
    push_cast; linarith

private theorem base_bounded (p : Data) (b : Conductor p) (G : Fin (p.k + 1) → ℤ)
    (hG : ∀ i, 0 ≤ G i ∧ d p ∣ G i) (i0 : Fin (p.k + 1)) (hi0 : G i0 = p.w)
    (hcov : ∀ x, d p ∣ x → b.c ≤ x → x ∈ AddSubmonoid.closure (Set.range G)) :
    ∀ a ∈ AddSubmonoid.closure (Set.range G), ∃ s : ℕ,
      (∃ f : Fin s → Fin (p.k + 1), ∑ j, G (f j) = a) ∧
      (s : ℤ) * p.w ≤ a + ((b.c + p.w) / d p) * p.w := by
  have hA := arithmetic p
  have hd := hA.1
  have hw := hA.2.1
  obtain ⟨Q, hQ⟩ : d p ∣ b.c + p.w := dvd_add b.dvd hA.2.2.1
  rw [hQ, Int.mul_ediv_cancel_left _ hd.ne']
  have hc := b.nonneg
  have small : ∀ a ∈ AddSubmonoid.closure (Set.range G), a < b.c + p.w →
      ∃ s : ℕ, (∃ f : Fin s → Fin (p.k + 1), ∑ j, G (f j) = a) ∧
        (s : ℤ) * p.w ≤ a + Q * p.w := by
    intro a ha hlt
    obtain ⟨s, hf, hs⟩ := base_short p G hG a ha
    refine ⟨s, hf, ?_⟩
    have h0 : (0 : ℤ) ≤ s := by positivity
    have h1 : (s : ℤ) ≤ Q := by
      by_contra hcon
      push Not at hcon
      have : (Q + 1) * d p ≤ s * d p := by nlinarith
      nlinarith
    have ha0 := (base_gen_nonneg p G hG a ha).1
    nlinarith
  have key : ∀ N : ℕ, ∀ a ∈ AddSubmonoid.closure (Set.range G), a < N * p.w + (b.c + p.w) →
      ∃ s : ℕ, (∃ f : Fin s → Fin (p.k + 1), ∑ j, G (f j) = a) ∧
        (s : ℤ) * p.w ≤ a + Q * p.w := by
    intro N
    induction N with
    | zero =>
      intro a ha hlt
      exact small a ha (by simpa using hlt)
    | succ N ih =>
      intro a ha hlt
      by_cases hsmall : a < b.c + p.w
      · exact small a ha hsmall
      · push Not at hsmall
        have hda := (base_gen_nonneg p G hG a ha).2
        have hmem : a - p.w ∈ AddSubmonoid.closure (Set.range G) :=
          hcov _ (dvd_sub hda hA.2.2.1) (by linarith)
        obtain ⟨s, ⟨f, hf⟩, hs⟩ := ih (a - p.w) hmem (by push_cast at hlt; linarith)
        refine ⟨s + 1, ⟨Fin.append f (fun _ => i0), ?_⟩, ?_⟩
        · rw [base_sum_append, hf]; simp [hi0]
        · push_cast; linarith
  intro a ha
  have ha0 := (base_gen_nonneg p G hG a ha).1
  refine key a.toNat a ha ?_
  rw [Int.toNat_of_nonneg ha0]
  nlinarith

theorem bounded_length (p : Data) (b : Conductor p) :
    (∀ a ∈ S p, ∃ s : ℕ, a ∈ sums p s ∧
      (s : ℤ) * p.w ≤ a + ((b.c + p.w) / d p) * p.w) ∧
    (∀ a ∈ Sr p, ∃ s : ℕ,
      (∃ f : Fin s → Fin (p.k + 1), ∑ j, (p.w - p.r (f j)) = a) ∧
      (s : ℤ) * p.w ≤ a + ((b.c + p.w) / d p) * p.w) := by
  have hA := arithmetic p
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact base_bounded p b p.r (fun i => ⟨(hA.2.2.2.1 i).1, (hA.2.2.2.1 i).2.2⟩)
      (Fin.last p.k) p.hw (fun x hx hcx => (b.covers x hx hcx).1) a ha
  · exact base_bounded p b (fun i => p.w - p.r i)
      (fun i => ⟨by linarith [(hA.2.2.2.1 i).2.1], dvd_sub hA.2.2.1 (hA.2.2.2.1 i).2.2⟩)
      0 (by simp [p.hr0]) (fun x hx hcx => (b.covers x hx hcx).2) a ha

private theorem base_pad (ι : Type) (G : ι → ℤ) (iz : ι) (hz : G iz = 0) (s s' : ℕ)
    (hs : s' ≤ s) (f : Fin s' → ι) :
    ∃ f' : Fin s → ι, ∑ j, G (f' j) = ∑ j, G (f j) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact ⟨Fin.append f (fun _ => iz), by rw [base_sum_append]; simp [hz]⟩

theorem saturation (p : Data) (b : Conductor p) (y : Point)
    (hy : y ∈ star p) (hsize : s0 p b * p.w ≤ y.1 + y.2) : y ∈ T p := by
  have hA := arithmetic p
  have hd := hA.1
  have hw := hA.2.1
  obtain ⟨⟨_, _, ⟨s, hs⟩⟩, hy1, hy2⟩ := hy
  obtain ⟨Q, hQ⟩ : d p ∣ b.c + p.w := dvd_add b.dvd hA.2.2.1
  have hs0 : s0 p b = 2 * Q := by
    unfold s0; rw [hQ, show 2 * (d p * Q) = d p * (2 * Q) by ring,
      Int.mul_ediv_cancel_left _ hd.ne']
  have hQ' : (b.c + p.w) / d p = Q := by rw [hQ, Int.mul_ediv_cancel_left _ hd.ne']
  rw [hs0] at hsize
  have hsQ : 2 * Q ≤ s := by nlinarith
  have hy1' := (base_S_nonneg p y.1 hy1).1
  have hy2' := (base_Sr_nonneg p y.2 hy2).1
  have hs0' : 0 ≤ s := by nlinarith
  rw [(monoid_model p).1]
  refine ⟨s.toNat, ?_, ?_⟩
  · rcases le_total y.1 y.2 with hle | hle
    · obtain ⟨s', ⟨f, hf⟩, hs'⟩ := (bounded_length p b).1 y.1 hy1
      rw [hQ'] at hs'
      have : (s' : ℤ) ≤ s := by nlinarith
      obtain ⟨f', hf'⟩ := base_pad (Fin (p.k + 1)) p.r 0 p.hr0 s.toNat s' (by omega) f
      exact ⟨f', by rw [hf', hf]⟩
    · obtain ⟨s', ⟨f, hf⟩, hs'⟩ := (bounded_length p b).2 y.2 hy2
      rw [hQ'] at hs'
      have : (s' : ℤ) ≤ s := by nlinarith
      obtain ⟨f', hf'⟩ := base_pad (Fin (p.k + 1)) (fun i => p.w - p.r i) (Fin.last p.k)
        (by simp [p.hw]) s.toNat s' (by omega) f
      refine ⟨f', ?_⟩
      have h2 : ∑ j, (p.w - p.r (f' j)) = (s.toNat : ℤ) * p.w - ∑ j, p.r (f' j) := by
        simp [Finset.sum_sub_distrib]
      rw [hf, h2, Int.toNat_of_nonneg hs0'] at hf'
      linarith
  · rw [Int.toNat_of_nonneg hs0']; linarith

-- PROOF.md 67-75.
private theorem rules_proj_add_smul (p : Data) (l j : ℤ) (y : Point) :
    proj p l (y + j • v p l) = proj p l y := by
  unfold proj v
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  congr 1
  unfold M; ring

private theorem rules_chi_add_smul (p : Data) (l j : ℤ) (y : Point) :
    chi p l (y + j • v p l) ↔ chi p l y := by
  unfold chi; rw [rules_proj_add_smul]

private theorem rules_lattice_add_smul (p : Data) (l j : ℤ) (y : Point) (hy : y ∈ lattice p) :
    y + j • v p l ∈ lattice p := by
  obtain ⟨h1, h2, ⟨t, ht⟩⟩ := hy
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, v]
  · exact dvd_add h1 ⟨-(j * m p l), by ring⟩
  · exact dvd_add h2 ⟨j * M p l, by ring⟩
  · exact ⟨t + j * d p, by unfold M; linear_combination ht⟩

private theorem rules_T_nonneg (p : Data) (y : Point) (hy : y ∈ T p) : 0 ≤ y.1 ∧ 0 ≤ y.2 := by
  obtain ⟨-, h1, h2⟩ := (monoid_model p).2.1 y hy
  exact ⟨((monoid_model p).2.2.1 _ h1).1, ((monoid_model p).2.2.2 _ h2).1⟩

private theorem rules_chi_of_T (p : Data) (l : ℤ) (hl : 0 ≤ l) (y : Point) (hy : y ∈ T p) :
    chi p l y := by
  unfold chi; rw [(lattice_model p l hl).2.2.2.2.1]; exact ⟨y, hy, rfl⟩

theorem strip_membership (p : Data) (b : Conductor p) (l : ℤ) (hl : 0 ≤ l)
    (hsize : max b.c (s0 p b * p.w) ≤ d p * m p l) (y : Point)
    (hy : y ∈ strip p l) :
    chi p l y ↔ y ∈ T p ∨ y.2 - d p * M p l ∈ Sr p := by
  obtain ⟨hyL, hy1, hy2⟩ := hy
  obtain ⟨hd, hw, -, -, hm⟩ := arithmetic p
  have hml := (hm l hl).1
  have hc : b.c ≤ d p * m p l := le_trans (le_max_left _ _) hsize
  have hs : s0 p b * p.w ≤ d p * m p l := le_trans (le_max_right _ _) hsize
  have hdM : d p * M p l = d p * m p l + d p * p.w := by unfold M; ring
  have hdw' : 0 < d p * p.w := mul_pos hd hw
  have hdm : 0 < d p * m p l := mul_pos hd hml
  have hMS : d p * M p l ∈ Sr p := (b.covers _ (dvd_mul_right _ _) (by linarith)).2
  constructor
  · intro h
    obtain ⟨j, hj⟩ := ((membership_and_lifts p l hl).1 y hyL).1 h
    have hn := rules_T_nonneg p _ hj
    rcases lt_trichotomy j 0 with hj0 | rfl | hj0
    · right
      have h2 : (y + j • v p l).2 ∈ Sr p := ((monoid_model p).2.1 _ hj).2.2
      have h3 := AddSubmonoid.add_mem _ h2 (AddSubmonoid.nsmul_mem _ hMS (-j - 1).toNat)
      convert h3 using 1
      rw [nsmul_eq_mul, Int.toNat_of_nonneg (by omega)]
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, v]
      ring
    · left; simpa using hj
    · exfalso
      have h1 := hn.1
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, v] at h1
      nlinarith
  · rintro (h | h)
    · exact rules_chi_of_T p l hl y h
    · have hL' := rules_lattice_add_smul p l (-1) y hyL
      have hy'2 := ((monoid_model p).2.2.2 _ h).1
      have hT : y + (-1 : ℤ) • v p l ∈ T p := by
        apply saturation p b
        · refine ⟨hL', ?_, ?_⟩
          · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, v]
            exact (b.covers _ (dvd_add hyL.1 ⟨m p l, by ring⟩) (by linarith)).1
          · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, v]
            convert h using 1; ring
        · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, v]
          linarith
      exact (rules_chi_add_smul p l (-1) y).1 (rules_chi_of_T p l hl _ hT)

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
  obtain ⟨hd, hw, hdw, -, -⟩ := arithmetic p
  have hdlew : d p ≤ p.w := Int.le_of_dvd hw hdw
  have hc := b.nonneg
  have hs0 : 1 ≤ s0 p b := by
    unfold s0
    rw [Int.le_ediv_iff_mul_le hd]
    linarith
  have hs0w : p.w ≤ s0 p b * p.w := by nlinarith
  have hcbar : p.w ≤ cbar p b := by unfold cbar; linarith
  refine ⟨hw, hcbar, ?_, ?_, ?_, le_max_left _ _, ?_⟩
  · unfold cbar; linarith
  · unfold cbar; linarith
  · unfold K; linarith
  · intro l
    unfold L
    rw [max_le_iff]
    have hdw' : 0 < d p * p.w := mul_pos hd hw
    have key : (6 * K p b - d p * p.n + d p * p.w - 1) / (d p * p.w) ≤ l ↔
        6 * K p b ≤ d p * m p l := by
      rw [← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hdw']
      have e1 : (l + 1) * (d p * p.w) = l * (d p * p.w) + d p * p.w := by ring
      have e2 : d p * m p l = d p * p.n + l * (d p * p.w) := by unfold m; ring
      rw [e1, e2]
      constructor <;> intro h <;> linarith
    rw [key]

private theorem rules_big (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    0 ≤ l ∧ 0 < p.w ∧ 0 ≤ b.c ∧ p.w ≤ cbar p b ∧ b.c ≤ cbar p b ∧
    s0 p b * p.w ≤ cbar p b ∧ D p b = cbar p b + p.w ∧ K p b = cbar p b + D p b ∧
    6 * K p b ≤ d p * m p l ∧ d p * M p l = d p * m p l + d p * p.w ∧
    0 < d p * p.w ∧ 0 < d p := by
  obtain ⟨hw, h1, h2, h3, -, -, h7⟩ := constants p b
  obtain ⟨hl0, h6⟩ := (h7 l).1 hl
  obtain ⟨hd, -, -, -, -⟩ := arithmetic p
  exact ⟨hl0, hw, b.nonneg, h1, h2, h3, rfl, rfl, h6, by unfold M; ring, mul_pos hd hw, hd⟩

private theorem rules_hsize (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    max b.c (s0 p b * p.w) ≤ d p * m p l := by
  obtain ⟨-, hw, -, h4, h5, h6, h7, h8, h9, -⟩ := rules_big p b l hl
  rw [max_le_iff]; constructor <;> linarith

-- PROOF.md 87.
theorem far_in_T (p : Data) (b : Conductor p) (y : Point) (hy : y ∈ lattice p)
    (h : (cbar p b ≤ y.1 ∧ y.2 ∈ Sr p) ∨ (y.1 ∈ S p ∧ cbar p b ≤ y.2)) :
    y ∈ T p := by
  obtain ⟨-, -, h2, h3, -, -, -⟩ := constants p b
  have hc := b.nonneg
  rcases h with ⟨h1, hs⟩ | ⟨hs, h1⟩
  · have := ((monoid_model p).2.2.2 _ hs).1
    exact saturation p b y ⟨hy, (b.covers _ hy.1 (by linarith)).1, hs⟩ (by linarith)
  · have := ((monoid_model p).2.2.1 _ hs).1
    exact saturation p b y ⟨hy, hs, (b.covers _ hy.2.1 (by linarith)).2⟩ (by linarith)

-- PROOF.md 89-104.
theorem rule_D (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p)
    (h : (cbar p b ≤ y.1 ∧ cbar p b ≤ y.2) ∨
      (cbar p b - d p * m p l ≤ y.1 ∧ d p * M p l + cbar p b ≤ y.2)) :
    chi p l y := by
  obtain ⟨hl0, hw, hc, h1, h2, h3, h4, h5, h6, h7, h8, hd⟩ := rules_big p b l hl
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact rules_chi_of_T p l hl0 y
      (far_in_T p b y hy (Or.inl ⟨ha, (b.covers _ hy.2.1 (by linarith)).2⟩))
  · have hL' := rules_lattice_add_smul p l (-1) y hy
    have hT : y + (-1 : ℤ) • v p l ∈ T p := by
      apply far_in_T p b _ hL'
      left
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, v]
      refine ⟨by linarith, (b.covers _ hL'.2.1 ?_).2⟩
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, v]
      linarith
    exact (rules_chi_add_smul p l (-1) y).1 (rules_chi_of_T p l hl0 _ hT)

theorem rule_N (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p)
    (ha : -d p * m p l ≤ y.1 ∧ y.1 < d p * m p l) (hb : y.2 < 0) :
    ¬ chi p l y := by
  obtain ⟨hl0, hw, hc, h1, h2, h3, h4, h5, h6, h7, h8, hd⟩ := rules_big p b l hl
  have hs := rules_hsize p b l hl
  have hnot : ∀ z : Point, z ∈ strip p l → z.2 < 0 → ¬ chi p l z := by
    intro z hz hz2 hchi
    rcases (strip_membership p b l hl0 hs z hz).1 hchi with hT | hS
    · have := (rules_T_nonneg p z hT).2; linarith
    · have := ((monoid_model p).2.2.2 _ hS).1; linarith
  rcases le_or_gt 0 y.1 with h0 | h0
  · exact hnot y ⟨hy, h0, ha.2⟩ hb
  · rw [← rules_chi_add_smul p l (-1) y]
    apply hnot
    · refine ⟨rules_lattice_add_smul p l (-1) y hy, ?_, ?_⟩ <;>
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, v] <;> linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, v]; linarith

theorem rule_O (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p) (hbox : |y.1| ≤ 2 * K p b ∧ |y.2| ≤ 2 * K p b) :
    chi p l y ↔ y ∈ T p := by
  obtain ⟨hl0, hw, hc, h1, h2, h3, h4, h5, h6, h7, h8, hd⟩ := rules_big p b l hl
  have hs := rules_hsize p b l hl
  obtain ⟨ha, hb⟩ := hbox
  rw [abs_le] at ha hb
  rcases lt_or_ge y.2 0 with hb0 | hb0
  · have := rules_T_nonneg p y
    constructor
    · intro hc'; exact absurd hc' (rule_N p b l hl y hy ⟨by linarith, by linarith⟩ hb0)
    · intro hT; linarith [(this hT).2]
  rcases lt_or_ge y.1 0 with ha0 | ha0
  · have := rules_T_nonneg p y
    constructor
    · intro hc'
      rw [← rules_chi_add_smul p l (-1) y] at hc'
      refine absurd hc' (rule_N p b l hl _ (rules_lattice_add_smul p l (-1) y hy) ?_ ?_) <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, v]
      · constructor <;> linarith
      · linarith
    · intro hT; linarith [(this hT).1]
  rw [strip_membership p b l hl0 hs y ⟨hy, ha0, by linarith⟩]
  constructor
  · rintro (h | h)
    · exact h
    · have := ((monoid_model p).2.2.2 _ h).1; linarith
  · exact Or.inl

private theorem rules_coset_lattice (p : Data) (l : ℤ) (hl : 0 ≤ l) (z : Point)
    (hz : z ∈ coset p) : P p l + z ∈ lattice p :=
  ((lattice_model p l hl).2.2.2.2.2 z).1 hz

theorem rule_P (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (z : Point) (hz : z ∈ coset p) (hbox : |z.1| ≤ 2 * K p b ∧ |z.2| ≤ 2 * K p b) :
    chi p l (P p l + z) ↔ z.1 ∈ S p ∨ z.2 ∈ Sr p := by
  obtain ⟨hl0, hw, hc, h1, h2, h3, h4, h5, h6, h7, h8, hd⟩ := rules_big p b l hl
  have hs := rules_hsize p b l hl
  have hyL := rules_coset_lattice p l hl0 z hz
  obtain ⟨ha, hb⟩ := hbox
  rw [abs_le] at ha hb
  rcases le_or_gt 0 z.1 with ha0 | ha0
  · rw [strip_membership p b l hl0 hs _ ⟨hyL, by simp [P]; linarith, by simp [P]; linarith⟩]
    have e : (P p l + z).2 - d p * M p l = z.2 := by simp [P]
    rw [e]
    constructor
    · rintro (h | h)
      · left; have := ((monoid_model p).2.1 _ h).2.1; simpa [P] using this
      · exact Or.inr h
    · rintro (h | h)
      · left
        apply far_in_T p b _ hyL
        right
        simp only [P, Prod.fst_add, Prod.snd_add, zero_add]
        exact ⟨h, by linarith⟩
      · exact Or.inr h
  · rw [← rules_chi_add_smul p l (-1)]
    have hL' := rules_lattice_add_smul p l (-1) _ hyL
    have e1 : (P p l + z + (-1 : ℤ) • v p l).1 = z.1 + d p * m p l := by
      simp only [P, Prod.fst_add, Prod.smul_fst, smul_eq_mul, v]; ring
    have e2 : (P p l + z + (-1 : ℤ) • v p l).2 = z.2 := by
      simp only [P, Prod.snd_add, Prod.smul_snd, smul_eq_mul, v]; ring
    rw [strip_membership p b l hl0 hs _ ⟨hL', by rw [e1]; linarith, by rw [e1]; linarith⟩]
    rw [e2]
    have hz1 : z.1 ∉ S p := fun h => by linarith [((monoid_model p).2.2.1 _ h).1]
    constructor
    · rintro (h | h)
      · right; have := ((monoid_model p).2.1 _ h).2.2; rwa [e2] at this
      · exfalso; linarith [((monoid_model p).2.2.2 _ h).1]
    · rintro (h | h)
      · exact absurd h hz1
      · left
        apply far_in_T p b _ hL'
        left
        rw [e1, e2]
        exact ⟨by linarith, h⟩

theorem rule_bottom (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p)
    (ha : cbar p b ≤ y.1 ∧ y.1 < d p * m p l) (hb : |y.2| ≤ 2 * K p b) :
    chi p l y ↔ y.2 ∈ Sr p := by
  obtain ⟨hl0, hw, hc, h1, h2, h3, h4, h5, h6, h7, h8, hd⟩ := rules_big p b l hl
  have hs := rules_hsize p b l hl
  rw [abs_le] at hb
  rw [strip_membership p b l hl0 hs y ⟨hy, by linarith, ha.2⟩]
  constructor
  · rintro (h | h)
    · exact ((monoid_model p).2.1 _ h).2.2
    · exfalso; linarith [((monoid_model p).2.2.2 _ h).1]
  · intro h
    exact Or.inl (far_in_T p b y hy (Or.inl ⟨ha.1, h⟩))

theorem rule_left (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ lattice p)
    (ha : |y.1| ≤ 2 * K p b) (hb : cbar p b ≤ y.2 ∧ y.2 < d p * M p l) :
    chi p l y ↔ y.1 ∈ S p := by
  obtain ⟨hl0, hw, hc, h1, h2, h3, h4, h5, h6, h7, h8, hd⟩ := rules_big p b l hl
  have hs := rules_hsize p b l hl
  rw [abs_le] at ha
  rcases le_or_gt 0 y.1 with ha0 | ha0
  · rw [strip_membership p b l hl0 hs y ⟨hy, ha0, by linarith⟩]
    constructor
    · rintro (h | h)
      · exact ((monoid_model p).2.1 _ h).2.1
      · exfalso; linarith [((monoid_model p).2.2.2 _ h).1]
    · intro h
      exact Or.inl (far_in_T p b y hy (Or.inr ⟨h, hb.1⟩))
  · have hz1 : y.1 ∉ S p := fun h => by linarith [((monoid_model p).2.2.1 _ h).1]
    simp only [hz1, iff_false]
    rw [← rules_chi_add_smul p l (-1) y]
    refine rule_N p b l hl _ (rules_lattice_add_smul p l (-1) y hy) ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, v]
    · constructor <;> linarith
    · linarith

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
  apply ((Set.finite_Ico 0 (cbar p b)).prod (Set.finite_Ico 0 (cbar p b))).subset
  rintro e ⟨-, h1, h2, -⟩
  exact ⟨h1, h2⟩

private theorem pf_phiP_finite (p : Data) (b : Conductor p) : (phiP p b).Finite := by
  apply ((Set.finite_Ico (-p.w) b.c).prod (Set.finite_Ico (-p.w) b.c)).subset
  rintro e ⟨-, h1, h2, -⟩
  exact ⟨h1, h2⟩

private theorem pf_consts (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    0 ≤ l ∧ 0 < d p ∧ 0 < p.w ∧ 0 ≤ b.c ∧ b.c ≤ cbar p b ∧ p.w ≤ cbar p b ∧
    s0 p b * p.w ≤ cbar p b ∧ K p b = 2 * cbar p b + p.w ∧ 6 * K p b ≤ d p * m p l ∧
    d p * M p l = d p * m p l + d p * p.w ∧ 0 < d p * p.w := by
  obtain ⟨hw, hwc, hcc, hs0, -, -, hL⟩ := constants p b
  obtain ⟨hl0, h6⟩ := (hL l).1 hl
  have hd := (arithmetic p).1
  refine ⟨hl0, hd, hw, b.nonneg, hcc, hwc, hs0, ?_, h6, ?_, mul_pos hd hw⟩
  · simp only [K, D]; ring
  · simp only [M]; ring

private theorem pf_lat_add (p : Data) (x y : Point) (hx : x ∈ lattice p) (hy : y ∈ lattice p) :
    x + y ∈ lattice p := by
  refine ⟨dvd_add hx.1 hy.1, dvd_add hx.2.1 hy.2.1, ?_⟩
  have := dvd_add hx.2.2 hy.2.2
  simp only [Prod.fst_add, Prod.snd_add]
  convert this using 1; ring

private theorem pf_lat_sub (p : Data) (x y : Point) (hx : x ∈ lattice p) (hy : y ∈ lattice p) :
    x - y ∈ lattice p := by
  refine ⟨dvd_sub hx.1 hy.1, dvd_sub hx.2.1 hy.2.1, ?_⟩
  have := dvd_sub hx.2.2 hy.2.2
  simp only [Prod.fst_sub, Prod.snd_sub]
  convert this using 1; ring

private theorem pf_coset_add (p : Data) (z y : Point) (hz : z ∈ coset p) (hy : y ∈ lattice p) :
    z + y ∈ coset p := by
  refine ⟨dvd_add hz.1 hy.1, dvd_add hz.2.1 hy.2.1, ?_⟩
  have := dvd_add hz.2.2 hy.2.2
  simp only [Prod.fst_add, Prod.snd_add]
  convert this using 1; ring

private theorem pf_g_lat (p : Data) (i : Fin (p.k + 1)) : g p i ∈ lattice p :=
  ((monoid_model p).2.1 _ (AddSubmonoid.subset_closure ⟨i, rfl⟩)).1

private theorem pf_proj_add_v (p : Data) (l : ℤ) (x : Point) (j : ℤ) :
    proj p l (x + j • v p l) = proj p l x := by
  unfold proj
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, v, M]
  ring

private theorem pf_proj_sub (p : Data) (l : ℤ) (hl : 0 ≤ l) (x y : Point)
    (hx : x ∈ lattice p) (hy : y ∈ lattice p) :
    proj p l (x - y) = proj p l x - proj p l y := by
  have := (lattice_model p l hl).1 (x - y) (pf_lat_sub p x y hx hy) y hy
  rw [sub_add_cancel] at this
  linarith

private theorem pf_kernel (p : Data) (l : ℤ) (hl : 0 ≤ l) (x : Point) (hx : x ∈ lattice p)
    (h0 : proj p l x = 0) (hb : |x.1| < d p * m p l) : x = 0 := by
  obtain ⟨j, rfl⟩ := ((lattice_model p l hl).2.2.1 x hx).1 h0
  have hA : 0 < d p * m p l := mul_pos (arithmetic p).1 ((arithmetic p).2.2.2.2 l hl).1
  simp only [Prod.smul_fst, smul_eq_mul, v] at hb
  rw [abs_mul, show -d p * m p l = -(d p * m p l) by ring, abs_neg, abs_of_pos hA] at hb
  have hj : |j| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have : j = 0 := by rw [abs_lt] at hj; omega
  subst this
  simp

private theorem pf_PF_iff (p : Data) (l : ℤ) (hl : 0 ≤ l) (u : Point) (hu : u ∈ lattice p) :
    proj p l u ∈ pseudoFrobenius (H p l) ↔ ¬ chi p l u ∧ ∀ i, chi p l (u + g p i) := by
  rw [(numerical_and_pf_test p l hl).2.2]
  have : ∀ i, proj p l u + m p l + p.r i = proj p l (u + g p i) := by
    intro i
    rw [(lattice_model p l hl).1 u hu (g p i) (pf_g_lat p i),
      (lattice_model p l hl).2.2.2.1 i]
    ring
  simp only [chi, this]

private theorem pf_O_iff (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) (e : Point)
    (he : e ∈ lattice p)
    (hbox : (0 ≤ e.1 ∧ e.1 < cbar p b) ∧ (0 ≤ e.2 ∧ e.2 < cbar p b)) :
    proj p l e ∈ pseudoFrobenius (H p l) ↔ e ∈ phiO p b := by
  obtain ⟨hl0, hd, hw, hc, hcc, hwc, hs0, hK, h6, hdM, hdw⟩ := pf_consts p b l hl
  rw [pf_PF_iff p l hl0 e he]
  have h1 := rule_O p b l hl e he ⟨abs_le.2 ⟨by linarith, by linarith⟩,
    abs_le.2 ⟨by linarith, by linarith⟩⟩
  have h2 : ∀ i, chi p l (e + g p i) ↔ e + g p i ∈ T p := by
    intro i
    obtain ⟨hr0, hrw, -⟩ := (arithmetic p).2.2.2.1 i
    apply rule_O p b l hl _ (pf_lat_add p _ _ he (pf_g_lat p i))
    simp only [Prod.fst_add, Prod.snd_add, g]
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  simp only [phiO, Set.mem_ofPred_eq, h1, h2]
  tauto

private theorem pf_P_iff (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) (z : Point)
    (hz : z ∈ coset p)
    (hbox : (-p.w ≤ z.1 ∧ z.1 < b.c) ∧ (-p.w ≤ z.2 ∧ z.2 < b.c)) :
    proj p l (P p l + z) ∈ pseudoFrobenius (H p l) ↔ z ∈ phiP p b := by
  obtain ⟨hl0, hd, hw, hc, hcc, hwc, hs0, hK, h6, hdM, hdw⟩ := pf_consts p b l hl
  have hPz := ((lattice_model p l hl0).2.2.2.2.2 z).1 hz
  rw [pf_PF_iff p l hl0 _ hPz]
  have h1 := rule_P p b l hl z hz ⟨abs_le.2 ⟨by linarith, by linarith⟩,
    abs_le.2 ⟨by linarith, by linarith⟩⟩
  have h2 : ∀ i, chi p l (P p l + z + g p i) ↔
      z.1 + p.r i ∈ S p ∨ z.2 + p.w - p.r i ∈ Sr p := by
    intro i
    obtain ⟨hr0, hrw, -⟩ := (arithmetic p).2.2.2.1 i
    rw [add_assoc]
    rw [rule_P p b l hl _ (pf_coset_add p _ _ hz (pf_g_lat p i))]
    · simp only [Prod.fst_add, Prod.snd_add, g, add_sub_assoc]
    · simp only [Prod.fst_add, Prod.snd_add, g]
      exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  simp only [phiP, Set.mem_ofPred_eq, h1, h2]
  tauto

private theorem pf_v_lat (p : Data) (l : ℤ) : v p l ∈ lattice p := by
  refine ⟨?_, dvd_mul_right _ _, ?_⟩
  · simp only [v, neg_mul]; exact dvd_neg.2 (dvd_mul_right _ _)
  · simp only [v, M]
    exact ⟨d p, by ring⟩

private theorem pf_lifts_lat (p : Data) (b : Conductor p) (l : ℤ) (hl : 0 ≤ l) (u : Point)
    (hu : u ∈ pfLifts p b l) : u ∈ lattice p := by
  rcases hu with he | ⟨z, hz, rfl⟩
  · exact he.1
  · exact ((lattice_model p l hl).2.2.2.2.2 z).1 hz.1

theorem pf_bijection (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (phiP p b).Finite ∧
    Set.BijOn (proj p l) (pfLifts p b l) (pseudoFrobenius (H p l)) := by
  obtain ⟨hl0, hd, hw, hc, hcc, hwc, hs0, hK, h6, hdM, hdw⟩ := pf_consts p b l hl
  have hSnn := (monoid_model p).2.2.1
  have hSrnn := (monoid_model p).2.2.2
  have hstar := (monoid_model p).2.1
  have hcoset := (lattice_model p l hl0).2.2.2.2.2
  refine ⟨pf_phiP_finite p b, ?_, ?_, ?_⟩
  · -- MapsTo
    intro u hu
    rcases hu with he | ⟨z, hz, rfl⟩
    · exact (pf_O_iff p b l hl u he.1 ⟨he.2.1, he.2.2.1⟩).2 he
    · exact (pf_P_iff p b l hl z hz.1 ⟨hz.2.1, hz.2.2.1⟩).2 hz
  · -- InjOn
    intro u hu u' hu' heq
    have hlu := pf_lifts_lat p b l hl0 u hu
    have hlu' := pf_lifts_lat p b l hl0 u' hu'
    have h0 : proj p l (u - u') = 0 := by
      rw [pf_proj_sub p l hl0 u u' hlu hlu', heq, sub_self]
    have key : |(u - u').1| < d p * m p l → u = u' := fun hb =>
      sub_eq_zero.1 (pf_kernel p l hl0 _ (pf_lat_sub p u u' hlu hlu') h0 hb)
    rcases hu with he | ⟨z, hz, rfl⟩ <;> rcases hu' with he' | ⟨z', hz', rfl⟩
    · apply key
      obtain ⟨-, ⟨h1, h2⟩, -⟩ := he
      obtain ⟨-, ⟨h1', h2'⟩, -⟩ := he'
      simp only [Prod.fst_sub]
      exact abs_lt.2 ⟨by linarith, by linarith⟩
    · exfalso
      obtain ⟨-, ⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := he
      obtain ⟨-, ⟨h1', h2'⟩, ⟨h3', h4'⟩, -⟩ := hz'
      have := key (by
        simp only [Prod.fst_sub, Prod.fst_add, P, zero_add]
        exact abs_lt.2 ⟨by linarith, by linarith⟩)
      have h2e := congrArg Prod.snd this
      simp only [Prod.snd_add, P] at h2e
      nlinarith
    · exfalso
      obtain ⟨-, ⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := he'
      obtain ⟨-, ⟨h1', h2'⟩, ⟨h3', h4'⟩, -⟩ := hz
      have := key (by
        simp only [Prod.fst_sub, Prod.fst_add, P, zero_add]
        exact abs_lt.2 ⟨by linarith, by linarith⟩)
      have h2e := congrArg Prod.snd this
      simp only [Prod.snd_add, P] at h2e
      nlinarith
    · apply key
      obtain ⟨-, ⟨h1, h2⟩, -⟩ := hz
      obtain ⟨-, ⟨h1', h2'⟩, -⟩ := hz'
      simp only [Prod.fst_sub, Prod.fst_add, P, zero_add]
      exact abs_lt.2 ⟨by linarith, by linarith⟩
  · -- SurjOn
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (membership_and_lifts p l hl0).2.2.surjOn (Set.mem_univ x)
    rw [← hyx] at hx
    obtain ⟨hyl, hy1, hy1'⟩ := hy
    have hPF := (pf_PF_iff p l hl0 y hyl).1 hx
    have hsize : max b.c (s0 p b * p.w) ≤ d p * m p l := max_le (by linarith) (by linarith)
    have SM := strip_membership p b l hl0 hsize
    have hnot := (SM y ⟨hyl, hy1, hy1'⟩).not.1 hPF.1
    rw [not_or] at hnot
    obtain ⟨hyT, hySr⟩ := hnot
    have hr0 := p.hr0
    have hrw := p.hw
    -- the point y + g 0
    have hg0 : y + g p 0 = (y.1, y.2 + p.w) := by
      ext <;> simp [g, hr0]
    have hg0s : y + g p 0 ∈ strip p l := ⟨pf_lat_add p _ _ hyl (pf_g_lat p 0),
      by rw [hg0]; exact hy1, by rw [hg0]; exact hy1'⟩
    have hc0 := (SM _ hg0s).1 (hPF.2 0)
    rw [hg0] at hc0
    by_cases hI : y.1 + p.w < d p * m p l
    · have hgl : y + g p (Fin.last p.k) = (y.1 + p.w, y.2) := by
        ext <;> simp [g, hrw]
      have hgls : y + g p (Fin.last p.k) ∈ strip p l := ⟨pf_lat_add p _ _ hyl (pf_g_lat p _),
        by rw [hgl]; dsimp only; linarith, by rw [hgl]; exact hI⟩
      have hcl := (SM _ hgls).1 (hPF.2 _)
      rw [hgl] at hcl
      have hy2 : y.2 ∈ Sr p := by
        rcases hcl with hT | hS
        · exact (hstar _ hT).2.2
        · exact absurd hS hySr
      have hy2nn := (hSrnn _ hy2).1
      by_cases hS : y.1 ∈ S p
      · have hsum : y.1 + y.2 < s0 p b * p.w := by
          by_contra hh
          push Not at hh
          exact hyT (saturation p b y ⟨hyl, hS, hy2⟩ hh)
        refine ⟨y, Set.mem_union_left _ ((pf_O_iff p b l hl y hyl ⟨⟨hy1, by linarith⟩,
          ⟨hy2nn, by linarith⟩⟩).1 hx), hyx⟩
      · have hy1c : y.1 < b.c := by
          by_contra hh
          push Not at hh
          exact hS (b.covers _ hyl.1 hh).1
        have hb2 : y.2 + p.w - d p * M p l ∈ Sr p := by
          rcases hc0 with hT | h
          · exact absurd (hstar _ hT).2.1 hS
          · exact h
        have hb2nn := (hSrnn _ hb2).1
        have hz2c : y.2 - d p * M p l < b.c := by
          by_contra hh
          push Not at hh
          exact hySr (b.covers _ (dvd_sub hyl.2.1 (dvd_mul_right _ _)) hh).2
        set z : Point := (y.1, y.2 - d p * M p l) with hzdef
        have hPz : P p l + z = y := by ext <;> simp [P, z]
        have hz : z ∈ coset p := (hcoset z).2 (by rw [hPz]; exact hyl)
        have hzP := (pf_P_iff p b l hl z hz ⟨⟨by simp only [z]; linarith, by simp only [z]; linarith⟩,
          ⟨by simp only [z]; linarith, by simp only [z]; linarith⟩⟩).1 (by rw [hPz]; exact hx)
        exact ⟨P p l + z, Set.mem_union_right _ ⟨z, hzP, rfl⟩, by rw [hPz]; exact hyx⟩
    · push Not at hI
      have hy1c : cbar p b ≤ y.1 := by linarith
      have hy2 : y.2 ∉ Sr p := fun h => hyT (far_in_T p b y hyl (Or.inl ⟨hy1c, h⟩))
      have hy2w : y.2 + p.w ∈ Sr p := by
        rcases hc0 with hT | h
        · exact (hstar _ hT).2.2
        · exfalso
          have := (hSrnn _ h).1
          exact hy2 (b.covers _ hyl.2.1 (by linarith)).2
      have hy2nn := (hSrnn _ hy2w).1
      have hy2c : y.2 < b.c := by
        by_contra hh
        push Not at hh
        exact hy2 (b.covers _ hyl.2.1 hh).2
      set z : Point := (y.1 - d p * m p l, y.2) with hzdef
      have hPz : P p l + z = y + (1 : ℤ) • v p l := by
        ext <;> simp [P, z, v] <;> ring
      have hPzl : P p l + z ∈ lattice p := by
        rw [hPz, one_smul]; exact pf_lat_add p _ _ hyl (pf_v_lat p l)
      have hpr : proj p l (P p l + z) = proj p l y := by rw [hPz, pf_proj_add_v]
      have hz : z ∈ coset p := (hcoset z).2 hPzl
      have hzP := (pf_P_iff p b l hl z hz ⟨⟨by simp only [z]; linarith, by simp only [z]; linarith⟩,
        ⟨by simp only [z]; linarith, by simp only [z]; linarith⟩⟩).1 (by rw [hpr]; exact hx)
      exact ⟨P p l + z, Set.mem_union_right _ ⟨z, hzP, rfl⟩, by rw [hpr]; exact hyx⟩

-- PROOF.md 292-294; permits omitting the vacuous branch in Lemma 7.
theorem phiP_nonempty (p : Data) (b : Conductor p) : (phiP p b).Nonempty := by
  obtain ⟨hd, hw, -, -, -⟩ := arithmetic p
  have hSnn := (monoid_model p).2.2.1
  have hSrnn := (monoid_model p).2.2.2
  have hn := p.hn
  have hCb : ∀ z : Point, z ∈ coset p → z.1 ∉ S p → z.2 ∉ Sr p → z.1 < b.c ∧ z.2 < b.c := by
    intro z hz h1 h2
    constructor
    · by_contra hh; push Not at hh; exact h1 (b.covers _ hz.1 hh).1
    · by_contra hh; push Not at hh; exact h2 (b.covers _ hz.2.1 hh).2
  have hz0c : ((-(d p * p.w), -(d p * p.n) - d p * p.w * p.n) : Point) ∈ coset p := by
    refine ⟨dvd_neg.2 (dvd_mul_right _ _), ?_, ?_⟩
    · exact dvd_sub (dvd_neg.2 (dvd_mul_right _ _)) (by rw [mul_assoc]; exact dvd_mul_right _ _)
    · exact ⟨-(d p * (1 + p.n)), by ring⟩
  have hdw : 0 < d p * p.w := mul_pos hd hw
  have hdn : 0 < d p * p.n := mul_pos hd hn
  have hdwn : 0 < d p * p.w * p.n := mul_pos hdw hn
  obtain ⟨s, ⟨z, ⟨hzc, hz1, hz2⟩, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun s => ∃ z : Point, (z ∈ coset p ∧ z.1 ∉ S p ∧ z.2 ∉ Sr p) ∧ z.1 + z.2 = s)
    ⟨2 * b.c, by
      rintro s ⟨z, ⟨hz, h1, h2⟩, rfl⟩
      have := hCb z hz h1 h2
      linarith⟩
    ⟨_, _, ⟨hz0c, fun h => by have := (hSnn _ h).1; dsimp only at this; linarith,
      fun h => by have := (hSrnn _ h).1; dsimp only at this; linarith⟩, rfl⟩
  have hfor : ∀ i, z.1 + p.r i ∈ S p ∨ z.2 + p.w - p.r i ∈ Sr p := by
    intro i
    by_contra hh
    push Not at hh
    have e1 : (z + g p i).1 = z.1 + p.r i := rfl
    have e2 : (z + g p i).2 = z.2 + p.w - p.r i := by
      show z.2 + (p.w - p.r i) = _; ring
    have := hmax _ ⟨z + g p i, ⟨pf_coset_add p z _ hzc (pf_g_lat p i),
      by rw [e1]; exact hh.1, by rw [e2]; exact hh.2⟩, rfl⟩
    rw [e1, e2] at this
    linarith
  obtain ⟨hzc1, hzc2⟩ := hCb z hzc hz1 hz2
  have hl := hfor (Fin.last p.k)
  have h0 := hfor 0
  rw [p.hw] at hl
  rw [p.hr0] at h0
  simp only [add_sub_cancel_right, add_zero, sub_zero] at hl h0
  have hl' : z.1 + p.w ∈ S p := hl.resolve_right hz2
  have h0' : z.2 + p.w ∈ Sr p := h0.resolve_left hz1
  have := (hSnn _ hl').1
  have := (hSrnn _ h0').1
  refine ⟨z, hzc, ⟨by linarith, hzc1⟩, ⟨by linarith, hzc2⟩, hz1, hz2, hfor⟩

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
  obtain ⟨hw0, hw, hcc, -, -, -, -⟩ := constants p b
  have hc := b.nonneg
  have hO : ∀ e ∈ phiO p b, e ∈ lattice p ∧ (0 ≤ e.1 ∧ e.1 < cbar p b) ∧
      (0 ≤ e.2 ∧ e.2 < cbar p b) := fun e he => ⟨he.1, he.2.1, he.2.2.1⟩
  have hP : ∀ e ∈ phiP p b, e ∈ coset p ∧ (-p.w ≤ e.1 ∧ e.1 < b.c) ∧
      (-p.w ≤ e.2 ∧ e.2 < b.c) := fun e he => ⟨he.1, he.2.1, he.2.2.1⟩
  have hD : D p b = cbar p b + p.w := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro z (⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩)
    · obtain ⟨⟨a1, a2, a3⟩, -⟩ := hO u hu
      obtain ⟨⟨b1, b2, b3⟩, -⟩ := hO v hv
      refine ⟨dvd_sub a1 b1, dvd_sub a2 b2, ?_⟩
      have := dvd_sub a3 b3
      simp only [Prod.fst_sub, Prod.snd_sub]
      convert this using 1; ring
    · obtain ⟨⟨a1, a2, a3⟩, -⟩ := hP u hu
      obtain ⟨⟨b1, b2, b3⟩, -⟩ := hP v hv
      refine ⟨dvd_sub a1 b1, dvd_sub a2 b2, ?_⟩
      have := dvd_sub a3 b3
      simp only [Prod.fst_sub, Prod.snd_sub]
      convert this using 1; ring
  · rintro z ⟨u, hu, v, hv, rfl⟩
    obtain ⟨⟨a1, a2, a3⟩, -⟩ := hP u hu
    obtain ⟨⟨b1, b2, b3⟩, -⟩ := hO v hv
    refine ⟨dvd_sub a1 b1, dvd_sub a2 b2, ?_⟩
    have := dvd_add a3 (dvd_neg.2 b3)
    simp only [Prod.fst_sub, Prod.snd_sub]
    convert this using 1; ring
  · rintro z ⟨u, hu, v, hv, rfl⟩
    obtain ⟨⟨a1, a2, a3⟩, -⟩ := hO u hu
    obtain ⟨⟨b1, b2, b3⟩, -⟩ := hP v hv
    simp only [coset, Set.mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg, Prod.fst_sub,
      Prod.snd_sub, neg_sub]
    refine ⟨dvd_sub b1 a1, dvd_sub b2 a2, ?_⟩
    have := dvd_add b3 (dvd_neg.2 a3)
    convert this using 1; ring
  · rintro z (((⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩) | ⟨u, hu, v, hv, rfl⟩) |
      ⟨u, hu, v, hv, rfl⟩)
    · obtain ⟨-, ⟨h1, h2⟩, h3, h4⟩ := hO u hu
      obtain ⟨-, ⟨h5, h6⟩, h7, h8⟩ := hO v hv
      simp only [Prod.fst_sub, Prod.snd_sub, hD]
      exact ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩
    · obtain ⟨-, ⟨h1, h2⟩, h3, h4⟩ := hP u hu
      obtain ⟨-, ⟨h5, h6⟩, h7, h8⟩ := hP v hv
      simp only [Prod.fst_sub, Prod.snd_sub, hD]
      exact ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩
    · obtain ⟨-, ⟨h1, h2⟩, h3, h4⟩ := hP u hu
      obtain ⟨-, ⟨h5, h6⟩, h7, h8⟩ := hO v hv
      simp only [Prod.fst_sub, Prod.snd_sub, hD]
      exact ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩
    · obtain ⟨-, ⟨h1, h2⟩, h3, h4⟩ := hO u hu
      obtain ⟨-, ⟨h5, h6⟩, h7, h8⟩ := hP v hv
      simp only [Prod.fst_sub, Prod.snd_sub, hD]
      exact ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩

def eval (p : Data) (b : Conductor p) (q0 qp qm : Point → Prop) : Prop :=
  (∃ u ∈ phiP p b, (∀ f ∈ phiP p b, q0 (u - f)) ∧
    (∀ e ∈ phiO p b, qp (u - e))) ∨
  (∃ e ∈ phiO p b, (∀ e2 ∈ phiO p b, q0 (e - e2)) ∧
    (∀ f ∈ phiP p b, qm (e - f)))
def tau (p : Data) (b : Conductor p) (l : ℤ) (y : Point) : Prop :=
  eval p b (fun z => chi p l (y + z))
    (fun z => chi p l (y + P p l + z)) (fun z => chi p l (y - P p l + z))

private theorem pf_trace_iff (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) (y : Point)
    (hy : y ∈ lattice p) :
    proj p l y ∈ trace (H p l) ↔ chi p l y ∧
      ∃ u ∈ pfLifts p b l, ∀ u' ∈ pfLifts p b l, chi p l (y + u - u') := by
  obtain ⟨hl0, -⟩ := pf_consts p b l hl
  have himg := (pf_bijection p b l hl).2.image_eq
  have key : ∀ u ∈ pfLifts p b l, ∀ u' ∈ pfLifts p b l,
      proj p l y + proj p l u - proj p l u' = proj p l (y + u - u') := by
    intro u hu u' hu'
    have hlu := pf_lifts_lat p b l hl0 u hu
    have hlu' := pf_lifts_lat p b l hl0 u' hu'
    rw [pf_proj_sub p l hl0 _ _ (pf_lat_add p _ _ hy hlu) hlu',
      (lattice_model p l hl0).1 y hy u hlu]
  constructor
  · rintro ⟨hH, q, hq, hf⟩
    rw [← himg] at hq
    obtain ⟨u, hu, rfl⟩ := hq
    refine ⟨hH, u, hu, fun u' hu' => ?_⟩
    have := hf _ (himg ▸ Set.mem_image_of_mem _ hu')
    rw [key u hu u' hu'] at this
    exact this
  · rintro ⟨hH, u, hu, hall⟩
    refine ⟨hH, proj p l u, himg ▸ Set.mem_image_of_mem _ hu, ?_⟩
    intro f hf
    rw [← himg] at hf
    obtain ⟨u', hu', rfl⟩ := hf
    rw [key u hu u' hu']
    exact hall u' hu'

private theorem pf_tau_iff (p : Data) (b : Conductor p) (l : ℤ) (y : Point) :
    (∃ u ∈ pfLifts p b l, ∀ u' ∈ pfLifts p b l, chi p l (y + u - u')) ↔ tau p b l y := by
  unfold tau eval
  constructor
  · rintro ⟨u, hu, hall⟩
    rcases hu with he | ⟨z, hz, rfl⟩
    · refine Or.inr ⟨u, he, fun e2 he2 => ?_, fun f hf => ?_⟩
      · have := hall e2 (Set.mem_union_left _ he2)
        rwa [show y + u - e2 = y + (u - e2) by abel] at this
      · have := hall (P p l + f) (Set.mem_union_right _ ⟨f, hf, rfl⟩)
        rwa [show y + u - (P p l + f) = y - P p l + (u - f) by abel] at this
    · refine Or.inl ⟨z, hz, fun f hf => ?_, fun e he => ?_⟩
      · have := hall (P p l + f) (Set.mem_union_right _ ⟨f, hf, rfl⟩)
        rwa [show y + (P p l + z) - (P p l + f) = y + (z - f) by abel] at this
      · have := hall e (Set.mem_union_left _ he)
        rwa [show y + (P p l + z) - e = y + P p l + (z - e) by abel] at this
  · rintro (⟨z, hz, h1, h2⟩ | ⟨e, he, h1, h2⟩)
    · refine ⟨P p l + z, Set.mem_union_right _ ⟨z, hz, rfl⟩, fun u' hu' => ?_⟩
      rcases hu' with he | ⟨f, hf, rfl⟩
      · have := h2 u' he
        rwa [show y + (P p l + z) - u' = y + P p l + (z - u') by abel]
      · have := h1 f hf
        rwa [show y + (P p l + z) - (P p l + f) = y + (z - f) by abel]
    · refine ⟨e, Set.mem_union_left _ he, fun u' hu' => ?_⟩
      rcases hu' with he2 | ⟨f, hf, rfl⟩
      · have := h1 u' he2
        rwa [show y + e - u' = y + (e - u') by abel]
      · have := h2 f hf
        rwa [show y + e - (P p l + f) = y - P p l + (e - f) by abel]

theorem trace_criterion (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (∀ y ∈ lattice p, proj p l y ∈ trace (H p l) ↔ chi p l y ∧ tau p b l y) ∧
    (∀ y ∈ lattice p, ∀ j : ℤ, tau p b l (y + j • v p l) ↔ tau p b l y) := by
  refine ⟨fun y hy => (pf_trace_iff p b l hl y hy).trans
    (and_congr_right' (pf_tau_iff p b l y)), fun y _ j => ?_⟩
  have hc : ∀ x, chi p l (x + j • v p l) ↔ chi p l x := fun x => by
    simp only [chi, pf_proj_add_v]
  have e0 : (fun z => chi p l (y + j • v p l + z)) = fun z => chi p l (y + z) := by
    funext z
    rw [show y + j • v p l + z = (y + z) + j • v p l by abel]
    exact propext (hc _)
  have ep : (fun z => chi p l (y + j • v p l + P p l + z)) =
      fun z => chi p l (y + P p l + z) := by
    funext z
    rw [show y + j • v p l + P p l + z = (y + P p l + z) + j • v p l by abel]
    exact propext (hc _)
  have em : (fun z => chi p l (y + j • v p l - P p l + z)) =
      fun z => chi p l (y - P p l + z) := by
    funext z
    rw [show y + j • v p l - P p l + z = (y - P p l + z) + j • v p l by abel]
    exact propext (hc _)
  unfold tau
  rw [e0, ep, em]

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

private theorem prof_nums (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    0 ≤ l ∧ 0 < p.w ∧ p.w ≤ cbar p b ∧ D p b = cbar p b + p.w ∧ K p b = cbar p b + D p b ∧
    6 * K p b ≤ d p * m p l ∧ d p * m p l + p.w ≤ d p * M p l := by
  obtain ⟨hw, hwc, -, -, -, -, hL⟩ := constants p b
  obtain ⟨hl0, h6⟩ := (hL l).1 hl
  have hd := (arithmetic p).1
  refine ⟨hl0, hw, hwc, rfl, rfl, h6, ?_⟩
  have : d p * M p l = d p * m p l + d p * p.w := by simp only [M]; ring
  rw [this]; nlinarith

private theorem prof_lat_add (p : Data) (x y : Point) (hx : x ∈ lattice p) (hy : y ∈ lattice p) :
    x + y ∈ lattice p := by
  simp only [lattice, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at *
  obtain ⟨a1, a2, a3⟩ := hx
  obtain ⟨b1, b2, b3⟩ := hy
  refine ⟨dvd_add a1 b1, dvd_add a2 b2, ?_⟩
  have := dvd_add a3 b3
  convert this using 1; ring

private theorem prof_lat_sub (p : Data) (x y : Point) (hx : x ∈ lattice p) (hy : y ∈ lattice p) :
    x - y ∈ lattice p := by
  simp only [lattice, Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub] at *
  obtain ⟨a1, a2, a3⟩ := hx
  obtain ⟨b1, b2, b3⟩ := hy
  refine ⟨dvd_sub a1 b1, dvd_sub a2 b2, ?_⟩
  have := dvd_sub a3 b3
  convert this using 1; ring

private theorem prof_lat_zero (p : Data) : (0 : Point) ∈ lattice p := by
  simp [lattice]

private theorem prof_lat_smul_v (p : Data) (l : ℤ) (y : Point) (j : ℤ) (hy : y ∈ lattice p) :
    y + j • v p l ∈ lattice p := by
  simp only [lattice, v, M, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at *
  obtain ⟨a1, a2, a3⟩ := hy
  refine ⟨dvd_add a1 ⟨-(j * m p l), by ring⟩, dvd_add a2 ⟨j * (m p l + p.w), by ring⟩, ?_⟩
  have : y.1 + j * (-d p * m p l) + (y.2 + j * (d p * (m p l + p.w))) =
      (y.1 + y.2) + (j * d p) * p.w := by ring
  rw [this]; exact dvd_add a3 (dvd_mul_left _ _)

private theorem prof_eval_congr (p : Data) (b : Conductor p) (q0 qp qm q0' qp' qm' : Point → Prop)
    (h0 : ∀ z ∈ delta0 p b, (q0 z ↔ q0' z)) (hp : ∀ z ∈ deltaPlus p b, (qp z ↔ qp' z))
    (hm : ∀ z ∈ deltaMinus p b, (qm z ↔ qm' z)) :
    eval p b q0 qp qm ↔ eval p b q0' qp' qm' := by
  unfold eval
  have a0 : ∀ u ∈ phiP p b, ∀ f ∈ phiP p b, u - f ∈ delta0 p b :=
    fun u hu f hf => Or.inr ⟨u, hu, f, hf, rfl⟩
  have a1 : ∀ e ∈ phiO p b, ∀ e2 ∈ phiO p b, e - e2 ∈ delta0 p b :=
    fun u hu f hf => Or.inl ⟨u, hu, f, hf, rfl⟩
  have ap : ∀ u ∈ phiP p b, ∀ e ∈ phiO p b, u - e ∈ deltaPlus p b :=
    fun u hu f hf => ⟨u, hu, f, hf, rfl⟩
  have am : ∀ e ∈ phiO p b, ∀ f ∈ phiP p b, e - f ∈ deltaMinus p b :=
    fun u hu f hf => ⟨u, hu, f, hf, rfl⟩
  constructor
  · rintro (⟨u, hu, h1, h2⟩ | ⟨e, he, h1, h2⟩)
    · exact Or.inl ⟨u, hu, fun f hf => (h0 _ (a0 u hu f hf)).1 (h1 f hf),
        fun e he => (hp _ (ap u hu e he)).1 (h2 e he)⟩
    · exact Or.inr ⟨e, he, fun f hf => (h0 _ (a1 e he f hf)).1 (h1 f hf),
        fun f hf => (hm _ (am e he f hf)).1 (h2 f hf)⟩
  · rintro (⟨u, hu, h1, h2⟩ | ⟨e, he, h1, h2⟩)
    · exact Or.inl ⟨u, hu, fun f hf => (h0 _ (a0 u hu f hf)).2 (h1 f hf),
        fun e he => (hp _ (ap u hu e he)).2 (h2 e he)⟩
    · exact Or.inr ⟨e, he, fun f hf => (h0 _ (a1 e he f hf)).2 (h1 f hf),
        fun f hf => (hm _ (am e he f hf)).2 (h2 f hf)⟩

theorem region_partition (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (⋃ i, regions p b l i) = positiveStrip p l ∧
    Pairwise (fun i j : Fin 5 => Disjoint (regions p b l i) (regions p b l j)) := by
  obtain ⟨hl0, hw, hwc, hD, hK, h6, hMm⟩ := prof_nums p b l hl
  refine ⟨?_, ?_⟩
  · ext y
    simp only [Set.mem_iUnion, Fin.exists_fin_succ, Fin.exists_fin_zero, regions,
      Matrix.cons_val_zero, Matrix.cons_val_succ, regionO, regionBottom, regionLeft, regionP,
      regionDeep, positiveStrip, strip, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨h0, h1, h2⟩ | ⟨⟨⟨h0, h1⟩, h2⟩, -⟩ | ⟨⟨⟨h0, h1⟩, h2⟩, -⟩ | ⟨⟨⟨h0, h1⟩, h2⟩, -⟩ |
        ⟨⟨⟨h0, h1⟩, h2⟩, -⟩ | h)
      · exact ⟨⟨h0, h1.1, by linarith⟩, h2.1⟩
      all_goals first | exact ⟨⟨h0, h1⟩, h2⟩ | exact h.elim
    · rintro ⟨⟨h0, h1, h2⟩, h3⟩
      simp only [h0, h1, h2, h3, true_and, and_true]
      generalize d p * m p l = A at *
      generalize d p * M p l = B at *
      omega
  · intro i j hij
    rw [Set.disjoint_left]
    fin_cases i <;> fin_cases j <;> simp at hij <;>
    · intro y h1 h2
      simp only [regions, Matrix.cons_val_zero, regionO, regionBottom,
        regionLeft, regionP, regionDeep, positiveStrip, strip, Set.mem_ofPred_eq,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] at h1 h2
      generalize d p * m p l = A at *
      generalize d p * M p l = B at *
      omega

-- PROOF.md 183-232.
theorem deep_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ regionDeep p b l) : chi p l y ∧ tau p b l y := by
  obtain ⟨hl0, hw, hwc, hD, hK, h6, hMm⟩ := prof_nums p b l hl
  obtain ⟨hd0, hdp, -, hbd⟩ := difference_bounds p b
  have hcos := (lattice_model p l hl0).2.2.2.2.2
  obtain ⟨⟨⟨hylat, hy1, hy1'⟩, hy2⟩, hreg⟩ := hy
  have c1 : ∀ δ : Point, δ ∈ lattice p → |δ.1| < D p b → |δ.2| < D p b →
      chi p l (y + δ) := by
    intro δ hδ h1 h2
    rw [abs_lt] at h1 h2
    apply rule_D p b l hl _ (prof_lat_add p y δ hylat hδ)
    simp only [Prod.fst_add, Prod.snd_add]
    rcases hreg with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  have c2 : ∀ δ : Point, δ ∈ coset p → |δ.1| < D p b → |δ.2| < D p b →
      chi p l (y + P p l + δ) := by
    intro δ hδ h1 h2
    rw [abs_lt] at h1 h2
    have hl' : y + P p l + δ ∈ lattice p := by
      rw [add_assoc]; exact prof_lat_add p _ _ hylat ((hcos δ).1 hδ)
    apply rule_D p b l hl _ hl'
    simp only [Prod.fst_add, Prod.snd_add, P]
    rcases hreg with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  refine ⟨?_, ?_⟩
  · have := c1 0 (prof_lat_zero p) (by simp; linarith) (by simp; linarith)
    simpa using this
  · unfold tau eval
    left
    obtain ⟨u, hu⟩ := phiP_nonempty p b
    refine ⟨u, hu, fun f hf => ?_, fun e he => ?_⟩
    · have hz : u - f ∈ delta0 p b := Or.inr ⟨u, hu, f, hf, rfl⟩
      exact c1 _ (hd0 _ hz) (hbd _ (Or.inl (Or.inl hz))).1 (hbd _ (Or.inl (Or.inl hz))).2
    · have hz : u - e ∈ deltaPlus p b := ⟨u, hu, e, he, rfl⟩
      exact c2 _ (hdp _ hz) (hbd _ (Or.inl (Or.inr hz))).1 (hbd _ (Or.inl (Or.inr hz))).2

private theorem prof_minus (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) (y : Point)
    (hy : y ∈ lattice p) (h1 : D p b - d p * m p l ≤ y.1) (h1' : y.1 + D p b ≤ d p * m p l)
    (h2 : y.2 < d p * M p l - K p b)
    (z : Point) (hz : z ∈ deltaMinus p b) : ¬ chi p l (y - P p l + z) := by
  obtain ⟨hl0, hw, hwc, hD, hK, h6, hMm⟩ := prof_nums p b l hl
  obtain ⟨-, -, hdm, hbd⟩ := difference_bounds p b
  have hcos := (lattice_model p l hl0).2.2.2.2.2
  have hb := hbd _ (Or.inr hz)
  rw [abs_lt, abs_lt] at hb
  have hlat : y - P p l + z ∈ lattice p := by
    have : y - P p l + z = y - (P p l + -z) := by abel
    rw [this]; exact prof_lat_sub p _ _ hy ((hcos _).1 (hdm z hz))
  apply rule_N p b l hl _ hlat
  · simp only [Prod.fst_add, Prod.fst_sub, P]
    constructor <;> nlinarith
  · simp only [Prod.snd_add, Prod.snd_sub, P]
    linarith

theorem bottom_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ regionBottom p b l) :
    (chi p l y ↔ y.2 ∈ Sr p) ∧ (tau p b l y ↔ beta p b y.2) := by
  obtain ⟨hl0, hw, hwc, hD, hK, h6, hMm⟩ := prof_nums p b l hl
  obtain ⟨hd0, hdp, hdm, hbd⟩ := difference_bounds p b
  have hcos := (lattice_model p l hl0).2.2.2.2.2
  obtain ⟨⟨⟨hylat, hy1, hy1'⟩, hy2⟩, ha, ha', hb⟩ := hy
  refine ⟨rule_bottom p b l hl y hylat ⟨by linarith, hy1'⟩ (by rw [abs_le]; constructor <;> linarith), ?_⟩
  unfold tau beta
  apply prof_eval_congr
  · intro z hz
    have hzb := hbd _ (Or.inl (Or.inl hz))
    rw [abs_lt, abs_lt] at hzb
    exact rule_bottom p b l hl _ (prof_lat_add p y z hylat (hd0 z hz))
      ⟨by simp only [Prod.fst_add]; linarith, by simp only [Prod.fst_add]; linarith⟩
      (by simp only [Prod.snd_add]; rw [abs_le]; constructor <;> linarith)
  · intro z hz
    have hzb := hbd _ (Or.inl (Or.inr hz))
    rw [abs_lt, abs_lt] at hzb
    have hl' : y + P p l + z ∈ lattice p := by
      rw [add_assoc]; exact prof_lat_add p _ _ hylat ((hcos z).1 (hdp z hz))
    simp only [iff_true]
    apply rule_D p b l hl _ hl'
    left
    simp only [Prod.fst_add, Prod.snd_add, P]
    constructor <;> linarith
  · intro z hz
    simp only [iff_false]
    exact prof_minus p b l hl y hylat (by linarith) (by linarith) (by linarith) z hz

theorem left_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ regionLeft p b l) :
    (chi p l y ↔ y.1 ∈ S p) ∧ (tau p b l y ↔ alpha p b y.1) := by
  obtain ⟨hl0, hw, hwc, hD, hK, h6, hMm⟩ := prof_nums p b l hl
  obtain ⟨hd0, hdp, hdm, hbd⟩ := difference_bounds p b
  have hcos := (lattice_model p l hl0).2.2.2.2.2
  obtain ⟨⟨⟨hylat, hy1, hy1'⟩, hy2⟩, ha, hb, hb'⟩ := hy
  refine ⟨rule_left p b l hl y hylat (by rw [abs_le]; constructor <;> linarith)
    ⟨by linarith, by linarith⟩, ?_⟩
  unfold tau alpha
  apply prof_eval_congr
  · intro z hz
    have hzb := hbd _ (Or.inl (Or.inl hz))
    rw [abs_lt, abs_lt] at hzb
    exact rule_left p b l hl _ (prof_lat_add p y z hylat (hd0 z hz))
      (by simp only [Prod.fst_add]; rw [abs_le]; constructor <;> linarith)
      ⟨by simp only [Prod.snd_add]; linarith, by simp only [Prod.snd_add]; linarith⟩
  · intro z hz
    have hzb := hbd _ (Or.inl (Or.inr hz))
    rw [abs_lt, abs_lt] at hzb
    have hl' : y + P p l + z ∈ lattice p := by
      rw [add_assoc]; exact prof_lat_add p _ _ hylat ((hcos z).1 (hdp z hz))
    simp only [iff_true]
    apply rule_D p b l hl _ hl'
    right
    simp only [Prod.fst_add, Prod.snd_add, P]
    constructor <;> linarith
  · intro z hz
    simp only [iff_false]
    exact prof_minus p b l hl y hylat (by linarith) (by linarith) (by linarith) z hz

theorem origin_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (y : Point) (hy : y ∈ regionO p b) :
    (chi p l y ↔ y ∈ T p) ∧ (tau p b l y ↔ thetaO p b y) := by
  obtain ⟨hl0, hw, hwc, hD, hK, h6, hMm⟩ := prof_nums p b l hl
  obtain ⟨hd0, hdp, hdm, hbd⟩ := difference_bounds p b
  have hcos := (lattice_model p l hl0).2.2.2.2.2
  obtain ⟨hylat, ⟨hy1, hy1'⟩, ⟨hy2, hy2'⟩⟩ := hy
  refine ⟨rule_O p b l hl y hylat ⟨by rw [abs_le]; constructor <;> linarith,
    by rw [abs_le]; constructor <;> linarith⟩, ?_⟩
  unfold tau thetaO
  apply prof_eval_congr
  · intro z hz
    have hzb := hbd _ (Or.inl (Or.inl hz))
    rw [abs_lt, abs_lt] at hzb
    exact rule_O p b l hl _ (prof_lat_add p y z hylat (hd0 z hz))
      ⟨by simp only [Prod.fst_add]; rw [abs_le]; constructor <;> linarith,
       by simp only [Prod.snd_add]; rw [abs_le]; constructor <;> linarith⟩
  · intro z hz
    have hzb := hbd _ (Or.inl (Or.inr hz))
    rw [abs_lt, abs_lt] at hzb
    have hc : y + z ∈ coset p := by
      rw [hcos]
      have : P p l + (y + z) = y + (P p l + z) := by abel
      rw [this]; exact prof_lat_add p _ _ hylat ((hcos z).1 (hdp z hz))
    have : y + P p l + z = P p l + (y + z) := by abel
    rw [this]
    exact rule_P p b l hl _ hc
      ⟨by simp only [Prod.fst_add]; rw [abs_le]; constructor <;> linarith,
       by simp only [Prod.snd_add]; rw [abs_le]; constructor <;> linarith⟩
  · intro z hz
    simp only [iff_false]
    exact prof_minus p b l hl y hylat (by linarith) (by linarith) (by linarith) z hz

theorem corner_profile (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    Set.BijOn (cornerMap p l) (ZP p b) (regionP p b l) ∧
    ∀ z ∈ ZP p b,
      (chi p l (cornerMap p l z) ↔ z.1 ∈ S p ∨ z.2 ∈ Sr p) ∧
      (tau p b l (cornerMap p l z) ↔ thetaP p b z) := by
  obtain ⟨hl0, hw, hwc, hD, hK, h6, hMm⟩ := prof_nums p b l hl
  obtain ⟨hd0, hdp, hdm, hbd⟩ := difference_bounds p b
  have hcos := (lattice_model p l hl0).2.2.2.2.2
  have hchiv := (membership_and_lifts p l hl0).2.1
  have htauv := (trace_criterion p b l hl).2
  have hcm : ∀ z : Point, ∃ j : ℤ, cornerMap p l z = P p l + z + j • v p l := by
    intro z; unfold cornerMap; split_ifs
    · exact ⟨-1, by ext <;> simp [P, v, M] <;> ring⟩
    · exact ⟨0, by simp⟩
  have hzbd : ∀ z ∈ ZP p b, -K p b ≤ z.1 ∧ z.1 ≤ K p b ∧ -K p b ≤ z.2 ∧ z.2 ≤ K p b := by
    intro z hz
    rcases hz.2 with ⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    have hPz : P p l + z ∈ lattice p := (hcos z).1 hz.1
    obtain ⟨b1, b2, b3, b4⟩ := hzbd z hz
    unfold cornerMap
    split_ifs with h
    · have hlat : (z.1 + d p * m p l, z.2) ∈ lattice p := by
        have := prof_lat_smul_v p l _ (-1) hPz
        convert this using 1; ext <;> simp [P, v, M] <;> ring
      have h3 : 0 ≤ z.2 ∧ z.2 < K p b := by
        rcases hz.2 with ⟨-, h3⟩ | ⟨⟨h1, -⟩, -⟩
        · exact h3
        · exact absurd h1 (not_le.2 h)
      refine ⟨⟨⟨hlat, ?_, ?_⟩, ?_⟩, Or.inl ⟨?_, ?_⟩⟩ <;> dsimp only <;> linarith
    · push Not at h
      have h5 : z.1 < K p b := by
        rcases hz.2 with ⟨⟨-, h1⟩, -⟩ | ⟨⟨-, h5⟩, -⟩
        · linarith
        · exact h5
      refine ⟨⟨⟨hPz, ?_, ?_⟩, ?_⟩, Or.inr ⟨?_, ?_, ?_⟩⟩ <;>
        simp only [P, Prod.fst_add, Prod.snd_add, zero_add] <;> linarith
  · intro z hz z' hz' h
    obtain ⟨b1, b2, b3, b4⟩ := hzbd z hz
    obtain ⟨c1, c2, c3, c4⟩ := hzbd z' hz'
    unfold cornerMap at h
    split_ifs at h with h1 h2 h2
    · obtain ⟨e1, e2⟩ := Prod.mk.inj h
      exact Prod.ext (by linarith) e2
    · have := congrArg Prod.fst h
      simp only [P, Prod.fst_add, zero_add] at this
      push Not at h2
      have : z'.1 < K p b := by
        rcases hz'.2 with ⟨⟨-, h5⟩, -⟩ | ⟨⟨-, h5⟩, -⟩
        · linarith
        · exact h5
      linarith
    · have := congrArg Prod.fst h
      simp only [P, Prod.fst_add, zero_add] at this
      push Not at h1
      have : z.1 < K p b := by
        rcases hz.2 with ⟨⟨-, h5⟩, -⟩ | ⟨⟨-, h5⟩, -⟩
        · linarith
        · exact h5
      linarith
    · exact add_left_cancel h
  · intro y hy
    obtain ⟨⟨⟨hylat, hy1, hy1'⟩, hy2⟩, hreg⟩ := hy
    rcases hreg with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · refine ⟨(y.1 - d p * m p l, y.2), ⟨?_, Or.inl ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩, ?_⟩
      · rw [hcos]
        have := prof_lat_smul_v p l y 1 hylat
        convert this using 1; ext <;> simp [P, v, M] <;> ring
      all_goals try (dsimp only; linarith)
      unfold cornerMap
      rw [if_pos (by dsimp only; linarith)]
      ext <;> simp
    · refine ⟨(y.1, y.2 - d p * M p l), ⟨?_, Or.inr ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩, ?_⟩
      · rw [hcos]
        convert hylat using 1; ext <;> simp [P]
      all_goals try (dsimp only; linarith)
      unfold cornerMap
      rw [if_neg (by dsimp only; linarith)]
      ext <;> simp [P]
  · intro z hz
    have hzc : z ∈ coset p := hz.1
    obtain ⟨b1, b2, b3, b4⟩ := hzbd z hz
    obtain ⟨j, hj⟩ := hcm z
    have hPz : P p l + z ∈ lattice p := (hcos z).1 hzc
    rw [hj, hchiv _ hPz j, htauv _ hPz j]
    refine ⟨rule_P p b l hl z hzc ⟨by rw [abs_le]; constructor <;> linarith,
      by rw [abs_le]; constructor <;> linarith⟩, ?_⟩
    unfold tau thetaP
    apply prof_eval_congr
    · intro δ hδ
      have hδb := hbd _ (Or.inl (Or.inl hδ))
      rw [abs_lt, abs_lt] at hδb
      have hc : z + δ ∈ coset p := by
        rw [hcos, ← add_assoc]; exact prof_lat_add p _ _ hPz (hd0 δ hδ)
      rw [show P p l + z + δ = P p l + (z + δ) by abel]
      exact rule_P p b l hl _ hc
        ⟨by simp only [Prod.fst_add]; rw [abs_le]; constructor <;> linarith,
         by simp only [Prod.snd_add]; rw [abs_le]; constructor <;> linarith⟩
    · intro δ hδ
      have hδb := hbd _ (Or.inl (Or.inr hδ))
      rw [abs_lt, abs_lt] at hδb
      simp only [iff_true]
      have hl' : P p l + z + P p l + δ ∈ lattice p := by
        rw [show P p l + z + P p l + δ = (P p l + z) + (P p l + δ) by abel]
        exact prof_lat_add p _ _ hPz ((hcos δ).1 (hdp δ hδ))
      apply rule_D p b l hl _ hl'
      right
      simp only [Prod.fst_add, Prod.snd_add, P]
      constructor <;> linarith
    · intro δ hδ
      have hδb := hbd _ (Or.inr hδ)
      rw [abs_lt, abs_lt] at hδb
      rw [show P p l + z - P p l + δ = z + δ by abel]
      have hl' : z + δ ∈ lattice p := by
        rw [show z + δ = (P p l + z) - (P p l + -δ) by abel]
        exact prof_lat_sub p _ _ hPz ((hcos _).1 (hdm δ hδ))
      exact rule_O p b l hl _ hl'
        ⟨by simp only [Prod.fst_add]; rw [abs_le]; constructor <;> linarith,
         by simp only [Prod.snd_add]; rw [abs_le]; constructor <;> linarith⟩

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
  obtain ⟨hw, hwc, -, -, -, -, -⟩ := constants p b
  have hK : 0 ≤ K p b := by simp only [K, D]; linarith
  refine ⟨(Set.finite_Ico 0 (K p b)).subset fun a ha => ⟨ha.2.1, ha.2.2.1⟩,
    (Set.finite_Ico 0 (K p b)).subset fun a ha => ⟨ha.2.1, ha.2.2.1⟩,
    ((Set.finite_Ico 0 (K p b)).prod (Set.finite_Ico 0 (K p b))).subset
      fun y hy => ⟨hy.1.2.1, hy.1.2.2⟩,
    ((Set.finite_Icc (-K p b) (K p b)).prod (Set.finite_Icc (-K p b) (K p b))).subset
      fun z hz => ?_⟩
  simp only [Set.mem_prod, Set.mem_Icc]
  rcases hz.1.2 with ⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩ <;>
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

private theorem cnt_facts (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    0 < d p ∧ 0 < p.w ∧ 0 ≤ K p b ∧ 6 * K p b ≤ d p * m p l ∧
    d p * M p l = d p * m p l + d p * p.w ∧ 0 ≤ d p * p.w ∧ p.w ≤ cbar p b ∧
    K p b = 2 * cbar p b + p.w ∧ 0 ≤ l := by
  obtain ⟨hw, hwc, -, -, -, -, hLiff⟩ := constants p b
  have hd := (arithmetic p).1
  obtain ⟨hl0, h6⟩ := (hLiff l).1 hl
  refine ⟨hd, hw, ?_, h6, by unfold M; ring, by positivity, hwc, by unfold K D; ring, hl0⟩
  unfold K D; linarith

theorem bad_lifts_bijection (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (badLifts p b l).Finite ∧
    Set.BijOn (proj p l) (badLifts p b l) (H p l \ trace (H p l)) := by
  obtain ⟨hd, hw, hK, h6, hM, hdw, hwc, hKe, hl0⟩ := cnt_facts p b l hl
  have hstrip := (membership_and_lifts p l hl0).2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((Set.finite_Ico 0 (d p * m p l)).prod (Set.finite_Icc 0 (d p * M p l + K p b))).subset ?_
    rintro y ⟨⟨⟨hyl, h1, h2⟩, h3⟩, hchi, htau⟩
    refine ⟨⟨h1, h2⟩, h3, ?_⟩
    by_contra hc
    push Not at hc
    apply htau
    refine (deep_profile p b l hl y ⟨⟨⟨hyl, h1, h2⟩, h3⟩, ?_⟩).2
    by_cases hy1 : K p b ≤ y.1
    · exact Or.inl ⟨hy1, by linarith⟩
    · exact Or.inr ⟨by linarith, hc⟩
  · rintro y ⟨⟨hy, -⟩, hchi, htau⟩
    exact ⟨hchi, fun ht => htau (((trace_criterion p b l hl).1 y hy.1).1 ht).2⟩
  · exact hstrip.injOn.mono (fun y hy => hy.1.1)
  · rintro x ⟨hxH, hxt⟩
    obtain ⟨y, hy, rfl⟩ := hstrip.surjOn (Set.mem_univ x)
    have hchi : chi p l y := hxH
    refine ⟨y, ⟨⟨hy, ?_⟩, hchi, fun ht => hxt (((trace_criterion p b l hl).1 y hy.1).2 ⟨hchi, ht⟩)⟩, rfl⟩
    by_contra hc
    push Not at hc
    exact rule_N p b l hl y hy.1 ⟨by nlinarith [hy.2.1], hy.2.2⟩ hc hchi

-- PROOF.md 238-240, 259. General nonnegative block count, including zero.
private theorem cnt_interval_succ (w X Y rho : ℤ) (hw : 0 < w) (hXY : X ≤ Y) :
    interval w X (Y + w) rho = insert (Y + (rho - Y) % w) (interval w X Y rho) := by
  ext x
  simp only [interval, Set.mem_insert_iff, Set.mem_ofPred_eq]
  have h0 : 0 ≤ (rho - Y) % w := Int.emod_nonneg _ hw.ne'
  have h1 : (rho - Y) % w < w := Int.emod_lt_of_pos _ hw
  constructor
  · rintro ⟨hx1, hx2, hx3⟩
    by_cases hxY : x < Y
    · exact Or.inr ⟨hx1, hxY, hx3⟩
    · left
      have hm : (x - Y) % w = (rho - Y) % w := by
        have := Int.ModEq.sub_right Y (show x ≡ rho [ZMOD w] from hx3)
        exact this
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at hm
      omega
  · rintro (rfl | ⟨hx1, hx2, hx3⟩)
    · refine ⟨by omega, by omega, ?_⟩
      have : (Y + (rho - Y) % w) ≡ Y + (rho - Y) [ZMOD w] :=
        Int.ModEq.add_left _ (Int.mod_modEq _ _)
      rw [show Y + (rho - Y) = rho by ring] at this
      exact this
    · exact ⟨hx1, by omega, hx3⟩

theorem interval_count_add (w X Y rho t : ℤ) (hw : 0 < w) (ht : 0 ≤ t) (hXY : X ≤ Y) :
    (interval w X Y rho).Finite ∧
    (intervalCount w X (Y + t * w) rho : ℤ) =
      (intervalCount w X Y rho : ℤ) + t := by
  have hfin : ∀ Y', (interval w X Y' rho).Finite := fun Y' =>
    (Set.finite_Ico X Y').subset (fun x hx => ⟨hx.1, hx.2.1⟩)
  refine ⟨hfin Y, ?_⟩
  obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le ht
  induction t with
  | zero => simp
  | succ t ih =>
    have hY : X ≤ Y + (t : ℤ) * w := by nlinarith
    have e : Y + ((t + 1 : ℕ) : ℤ) * w = (Y + (t : ℤ) * w) + w := by push_cast; ring
    unfold intervalCount at *
    rw [e, cnt_interval_succ w X _ rho hw hY, Set.ncard_insert_of_notMem _ (hfin _)]
    · push_cast; rw [ih (by positivity)]; ring
    · intro hm; have := hm.2.1; have := Int.emod_nonneg (rho - (Y + t * w)) hw.ne'; omega

noncomputable def total (p : Data) (b : Conductor p) (l : ℤ) : ℕ :=
  (badO p b).ncard + (badP p b).ncard +
    ∑ a ∈ (bad_finite p b).2.1.toFinset, intervalCount p.w (K p b) (d p * m p l - K p b) (-a) +
    ∑ a ∈ (bad_finite p b).1.toFinset, intervalCount p.w (K p b) (d p * M p l - K p b) (-a)

-- PROOF.md 247-262; in particular this proves finiteness of the residue.
private theorem cnt_encard_sigma (s : Finset ℤ) (F : ℤ → Set ℤ) :
    ({q : ℤ × ℤ | q.1 ∈ s ∧ q.2 ∈ F q.1}).encard = ∑ a ∈ s, (F a).encard := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have e : {q : ℤ × ℤ | q.1 ∈ insert a s ∧ q.2 ∈ F q.1} =
        ((fun x => (a, x)) '' F a) ∪ {q : ℤ × ℤ | q.1 ∈ s ∧ q.2 ∈ F q.1} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_insert, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨rfl | hx, hy⟩
        · exact Or.inl ⟨y, hy, rfl, rfl⟩
        · exact Or.inr ⟨hx, hy⟩
      · rintro (⟨z, hz, rfl, rfl⟩ | ⟨hx, hy⟩)
        · exact ⟨Or.inl rfl, hz⟩
        · exact ⟨Or.inr hx, hy⟩
    rw [e, Set.encard_union_eq, Function.Injective.encard_image, ih, Finset.sum_insert ha]
    · intro x y h; simpa using h
    · rw [Set.disjoint_left]
      rintro q ⟨x, hx, rfl⟩ ⟨h1, -⟩
      exact ha h1

private theorem cnt_mod_iff (w x a : ℤ) : x % w = (-a) % w ↔ w ∣ x + a := by
  show Int.ModEq w x (-a) ↔ _
  rw [Int.modEq_iff_dvd, show -a - x = -(x + a) by ring, dvd_neg]

theorem residue_count (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    traceResidue (H p l) = (total p b l : ℕ∞) := by
  obtain ⟨hd, hw, hK, h6, hM, hdw, hwc, hKe, hl0⟩ := cnt_facts p b l hl
  have hdw' := (arithmetic p).2.2.1
  obtain ⟨-, hbij⟩ := bad_lifts_bijection p b l hl
  unfold traceResidue
  rw [← hbij.image_eq, hbij.injOn.encard_image]
  have hdisj := (region_partition p b l hl).2
  have hcov := (region_partition p b l hl).1
  have h01 : Disjoint (regionO p b) (regionBottom p b l) := hdisj (show (0 : Fin 5) ≠ 1 by decide)
  have h02 : Disjoint (regionO p b) (regionLeft p b l) := hdisj (show (0 : Fin 5) ≠ 2 by decide)
  have h03 : Disjoint (regionO p b) (regionP p b l) := hdisj (show (0 : Fin 5) ≠ 3 by decide)
  have h12 : Disjoint (regionBottom p b l) (regionLeft p b l) :=
    hdisj (show (1 : Fin 5) ≠ 2 by decide)
  have h13 : Disjoint (regionBottom p b l) (regionP p b l) :=
    hdisj (show (1 : Fin 5) ≠ 3 by decide)
  have h23 : Disjoint (regionLeft p b l) (regionP p b l) :=
    hdisj (show (2 : Fin 5) ≠ 3 by decide)
  set B := badLifts p b l with hBdef
  have hsplit : B = ((B ∩ regionO p b ∪ B ∩ regionBottom p b l) ∪ B ∩ regionLeft p b l) ∪
      B ∩ regionP p b l := by
    ext y
    constructor
    · intro hy
      have hps : y ∈ positiveStrip p l := hy.1
      rw [← hcov, Set.mem_iUnion] at hps
      obtain ⟨i, hi⟩ := hps
      fin_cases i
      · exact Or.inl (Or.inl (Or.inl ⟨hy, hi⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hy, hi⟩))
      · exact Or.inl (Or.inr ⟨hy, hi⟩)
      · exact Or.inr ⟨hy, hi⟩
      · exact absurd (deep_profile p b l hl y hi).2 hy.2.2
    · rintro (((h | h) | h) | h) <;> exact h.1
  have hO : B ∩ regionO p b = badO p b := by
    ext y
    constructor
    · rintro ⟨hyB, hyR⟩
      have hpr := origin_profile p b l hl y hyR
      exact ⟨hyR, hpr.1.1 hyB.2.1, fun h => hyB.2.2 (hpr.2.2 h)⟩
    · rintro ⟨hR, hT, hth⟩
      have hpr := origin_profile p b l hl y hR
      exact ⟨⟨⟨⟨hR.1, hR.2.1.1, by linarith [hR.2.1.2]⟩, hR.2.2.1⟩, hpr.1.2 hT,
        fun h => hth (hpr.2.1 h)⟩, hR⟩
  have hP : B ∩ regionP p b l = cornerMap p l '' badP p b := by
    have hc := corner_profile p b l hl
    ext y
    constructor
    · rintro ⟨hyB, hyR⟩
      obtain ⟨z, hz, rfl⟩ := hc.1.surjOn hyR
      have := hc.2 z hz
      exact ⟨z, ⟨hz, this.1.1 hyB.2.1, fun h => hyB.2.2 (this.2.2 h)⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hS, hth⟩, rfl⟩
      have hR := hc.1.mapsTo hz
      have := hc.2 z hz
      exact ⟨⟨hR.1, this.1.2 hS, fun h => hth (this.2.1 h)⟩, hR⟩
  have hBot : B ∩ regionBottom p b l = Prod.swap '' {q : ℤ × ℤ | q.1 ∈ (bad_finite p b).2.1.toFinset ∧
      q.2 ∈ interval p.w (K p b) (d p * m p l - K p b) (-q.1)} := by
    ext y
    constructor
    · rintro ⟨hyB, hyR⟩
      obtain ⟨hchi', htau'⟩ := bottom_profile p b l hl y hyR
      have hSr := hchi'.1 hyB.2.1
      have hnb : ¬ beta p b y.2 := fun h => hyB.2.2 (htau'.2 h)
      obtain ⟨⟨⟨⟨hd1, hd2, hw12⟩, h1, h2⟩, h3⟩, h4, h5, h6'⟩ := hyR
      refine ⟨(y.2, y.1), ⟨?_, h4, h5, (cnt_mod_iff _ _ _).2 hw12⟩, rfl⟩
      simp only [Set.Finite.mem_toFinset]
      exact ⟨hd2, h3, h6', hSr, hnb⟩
    · rintro ⟨⟨a, x⟩, ⟨ha, hx1, hx2, hx3⟩, rfl⟩
      simp only [Set.Finite.mem_toFinset] at ha
      obtain ⟨hda, ha0, haK, haS, hab⟩ := ha
      have hwx := (cnt_mod_iff _ _ _).1 hx3
      have hdx : d p ∣ x := by
        have := dvd_sub (dvd_trans hdw' hwx) hda
        simpa using this
      have hR : (x, a) ∈ regionBottom p b l :=
        ⟨⟨⟨⟨hdx, hda, hwx⟩, by linarith, by linarith⟩, ha0⟩, hx1, hx2, haK⟩
      obtain ⟨hc, ht⟩ := bottom_profile p b l hl (x, a) hR
      exact ⟨⟨hR.1, hc.2 haS, fun h => hab (ht.1 h)⟩, hR⟩
  have hLeft : B ∩ regionLeft p b l = {q : ℤ × ℤ | q.1 ∈ (bad_finite p b).1.toFinset ∧
      q.2 ∈ interval p.w (K p b) (d p * M p l - K p b) (-q.1)} := by
    ext y
    constructor
    · rintro ⟨hyB, hyR⟩
      obtain ⟨hchi', htau'⟩ := left_profile p b l hl y hyR
      have hS := hchi'.1 hyB.2.1
      have hna : ¬ alpha p b y.1 := fun h => hyB.2.2 (htau'.2 h)
      obtain ⟨⟨⟨⟨hd1, hd2, hw12⟩, h1, h2⟩, h3⟩, h4, h5, h6'⟩ := hyR
      refine ⟨?_, h5, h6', (cnt_mod_iff _ _ _).2 (by rwa [add_comm])⟩
      simp only [Set.Finite.mem_toFinset]
      exact ⟨hd1, h1, h4, hS, hna⟩
    · intro hy
      obtain ⟨a, x⟩ := y
      obtain ⟨ha, hx1, hx2, hx3⟩ := hy
      simp only [Set.Finite.mem_toFinset] at ha
      obtain ⟨hda, ha0, haK, haS, hab⟩ := ha
      have hwx := (cnt_mod_iff _ _ _).1 hx3
      have hdx : d p ∣ x := by
        have := dvd_sub (dvd_trans hdw' hwx) hda
        simpa using this
      have hR : (a, x) ∈ regionLeft p b l :=
        ⟨⟨⟨⟨hda, hdx, by rwa [add_comm]⟩, ha0, by linarith⟩, by linarith⟩, haK, hx1, hx2⟩
      obtain ⟨hc, ht⟩ := left_profile p b l hl (a, x) hR
      exact ⟨⟨hR.1, hc.2 haS, fun h => hab (ht.1 h)⟩, hR⟩
  have dOB := h01.mono (Set.inter_subset_right (s := B)) (Set.inter_subset_right (s := B))
  have dOL := h02.mono (Set.inter_subset_right (s := B)) (Set.inter_subset_right (s := B))
  have dOP := h03.mono (Set.inter_subset_right (s := B)) (Set.inter_subset_right (s := B))
  have dBL := h12.mono (Set.inter_subset_right (s := B)) (Set.inter_subset_right (s := B))
  have dBP := h13.mono (Set.inter_subset_right (s := B)) (Set.inter_subset_right (s := B))
  have dLP := h23.mono (Set.inter_subset_right (s := B)) (Set.inter_subset_right (s := B))
  rw [hsplit, Set.encard_union_eq (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
      ⟨dOP, dBP⟩, dLP⟩), Set.encard_union_eq (Set.disjoint_union_left.2 ⟨dOL, dBL⟩),
    Set.encard_union_eq dOB, hO, hBot, hLeft, hP, Prod.swap_injective.encard_image,
    cnt_encard_sigma _ (fun a => interval p.w (K p b) (d p * m p l - K p b) (-a)),
    cnt_encard_sigma _ (fun a => interval p.w (K p b) (d p * M p l - K p b) (-a)),
    ((corner_profile p b l hl).1.injOn.mono (fun z hz => hz.1)).encard_image]
  have hI : ∀ Y a, ((intervalCount p.w (K p b) Y (-a) : ℕ) : ℕ∞) =
      (interval p.w (K p b) Y (-a)).encard := fun Y a =>
    ((Set.finite_Ico (K p b) Y).subset (fun x hx => ⟨hx.1, hx.2.1⟩)).cast_ncard_eq
  unfold total
  push_cast
  simp only [hI, (bad_finite p b).2.2.1.cast_ncard_eq, (bad_finite p b).2.2.2.cast_ncard_eq]
  ring

noncomputable def slope (p : Data) (b : Conductor p) : ℤ :=
  d p * ((badA p b).ncard + (badB p b).ncard : ℕ)

theorem count_affine (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (total p b l : ℤ) = (total p b (L p b) : ℤ) + slope p b * (l - L p b) := by
  obtain ⟨hw, hwc, -, -, hDK, hL0, hLiff⟩ := constants p b
  have hd := (arithmetic p).1
  have hLL := ((hLiff (L p b)).1 le_rfl).2
  have hK0 : 0 ≤ K p b := by unfold K D; linarith
  have ht : 0 ≤ (l - L p b) * d p := mul_nonneg (by linarith) hd.le
  have em : d p * m p l - K p b = (d p * m p (L p b) - K p b) + ((l - L p b) * d p) * p.w := by
    unfold m; ring
  have eM : d p * M p l - K p b = (d p * M p (L p b) - K p b) + ((l - L p b) * d p) * p.w := by
    unfold M m; ring
  have hXm : K p b ≤ d p * m p (L p b) - K p b := by linarith
  have hXM : K p b ≤ d p * M p (L p b) - K p b := by
    have : d p * M p (L p b) = d p * m p (L p b) + d p * p.w := by unfold M; ring
    nlinarith
  unfold total Plan.slope
  push_cast
  rw [em, eM]
  simp only [fun a => (interval_count_add p.w _ _ (-a) _ hw ht hXm).2,
    fun a => (interval_count_add p.w _ _ (-a) _ hw ht hXM).2]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Set.ncard_eq_toFinset_card _ (bad_finite p b).1,
    ← Set.ncard_eq_toFinset_card _ (bad_finite p b).2.1]
  ring

theorem explicit_affine (p : Data) (b : Conductor p) :
    0 ≤ slope p b ∧ 0 ≤ L p b ∧ ∀ l : ℤ, L p b ≤ l →
      ∃ N : ℕ, traceResidue (H p l) = N ∧
        (N : ℤ) = slope p b * l + ((total p b (L p b) : ℤ) - slope p b * L p b) := by
  refine ⟨mul_nonneg (arithmetic p).1.le (by positivity), (constants p b).2.2.2.2.2.1,
    fun l hl => ⟨total p b l, residue_count p b l hl, ?_⟩⟩
  rw [count_affine p b l hl]; ring

-- PROOF.md 281-283: proved corollaries, not additional records.
theorem eventual_type (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (pseudoFrobenius (H p l)).Finite ∧
    (pseudoFrobenius (H p l)).ncard = (phiO p b).ncard + (phiP p b).ncard := by
  obtain ⟨hPf, hbij⟩ := pf_bijection p b l hl
  obtain ⟨hd, hw, hK, h6, hM, hdw, hwc, hKe, -⟩ := cnt_facts p b l hl
  have hfin : (pfLifts p b l).Finite :=
    (phiO_finite p b).union (hPf.image _)
  rw [← hbij.image_eq]
  refine ⟨hfin.image _, ?_⟩
  rw [hbij.injOn.ncard_image]
  unfold pfLifts
  rw [Set.ncard_union_eq _ (phiO_finite p b) (hPf.image _),
    Set.ncard_image_of_injective _ (add_right_injective _)]
  rw [Set.disjoint_left]
  rintro e he ⟨z, hz, rfl⟩
  have h1 := he.2.2.1.2
  have h2 := hz.2.2.1.1
  simp only [P, Prod.snd_add] at h1
  linarith

theorem trace_add (Q : AddSubmonoid ℤ) (h t : ℤ)
    (hh : h ∈ trace (Q : Set ℤ)) (ht : t ∈ Q) :
    h + t ∈ trace (Q : Set ℤ) := by
  obtain ⟨hQ, q, hq, hf⟩ := hh
  refine ⟨Q.add_mem hQ ht, q, hq, fun f hf' => ?_⟩
  have := Q.add_mem (hf f hf') ht
  have e : h + t + q - f = h + q - f + t := by ring
  rw [e]; exact this

private theorem cnt_decomp (p : Data) (l : ℤ) (h : ℤ) (hh : h ∈ H p l) :
    h = 0 ∨ ∃ i, ∃ h' ∈ H p l, h = (m p l + p.r i) + h' := by
  unfold H shiftedSemigroup at *
  induction hh using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Or.inr ⟨i, 0, zero_mem _, by simp [m]⟩
  | zero => exact Or.inl rfl
  | add x y hx hy ihx ihy =>
    rcases ihx with rfl | ⟨i, h', hh', rfl⟩
    · simpa using ihy
    · exact Or.inr ⟨i, h' + y, add_mem hh' hy, by ring⟩

private theorem cnt_g_regionO (p : Data) (b : Conductor p) (i : Fin (p.k + 1)) :
    g p i ∈ regionO p b := by
  have hT : g p i ∈ T p := AddSubmonoid.subset_closure ⟨i, rfl⟩
  have hl := ((monoid_model p).2.1 _ hT).1
  obtain ⟨hw, hwc, -⟩ := constants p b
  obtain ⟨h0, h1, -⟩ := (arithmetic p).2.2.2.1 i
  have : K p b = 2 * cbar p b + p.w := by unfold K D; ring
  refine ⟨hl, ⟨h0, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [g] <;> linarith

private theorem cnt_g_trace (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l)
    (i : Fin (p.k + 1)) : m p l + p.r i ∈ trace (H p l) ↔ thetaO p b (g p i) := by
  obtain ⟨-, -, -, -, -, -, -, -, hl0⟩ := cnt_facts p b l hl
  have hreg := cnt_g_regionO p b i
  rw [← ((lattice_model p l hl0).2.2.2.1 i), (trace_criterion p b l hl).1 _ hreg.1,
    ← (origin_profile p b l hl _ hreg).2]
  have hT : g p i ∈ T p := AddSubmonoid.subset_closure ⟨i, rfl⟩
  have : chi p l (g p i) := ((origin_profile p b l hl _ hreg).1).2 hT
  exact ⟨fun h => h.2, fun h => ⟨this, h⟩⟩

theorem nearly_gorenstein (p : Data) (b : Conductor p) (l : ℤ) (hl : L p b ≤ l) :
    (∀ h ∈ H p l, h ≠ 0 → h ∈ trace (H p l)) ↔
      ∀ i, thetaO p b (g p i) := by
  obtain ⟨-, -, -, -, -, -, -, -, hl0⟩ := cnt_facts p b l hl
  have hgen : ∀ i, m p l + p.r i ∈ H p l := fun i =>
    AddSubmonoid.subset_closure ⟨i, rfl⟩
  constructor
  · intro h i
    rw [← cnt_g_trace p b l hl i]
    refine h _ (hgen i) ?_
    have := ((arithmetic p).2.2.2.2 l hl0).1
    have := ((arithmetic p).2.2.2.1 i).1
    omega
  · intro h x hx hne
    rcases cnt_decomp p l x hx with rfl | ⟨i, h', hh', rfl⟩
    · exact absurd rfl hne
    · exact trace_add (shiftedSemigroup p.k p.r p.n p.w l) _ _
        ((cnt_g_trace p b l hl i).2 (h i)) hh'

theorem constant_iff (p : Data) (b : Conductor p) :
    (∃ C : ℕ, ∀ l : ℤ, L p b ≤ l → traceResidue (H p l) = C) ↔
      badA p b = ∅ ∧ badB p b = ∅ := by
  have hd := (arithmetic p).1
  constructor
  · rintro ⟨C, hC⟩
    have h1 := hC (L p b) le_rfl
    have h2 := hC (L p b + 1) (by linarith)
    rw [residue_count p b _ le_rfl] at h1
    rw [residue_count p b _ (by linarith)] at h2
    have e1 : total p b (L p b) = C := by exact_mod_cast h1
    have e2 : total p b (L p b + 1) = C := by exact_mod_cast h2
    have := count_affine p b (L p b + 1) (by linarith)
    rw [e1, e2] at this
    have hs : slope p b = 0 := by linarith
    unfold Plan.slope at hs
    have hn : ((badA p b).ncard + (badB p b).ncard : ℕ) = 0 := by
      have := (mul_eq_zero.mp hs).resolve_left hd.ne'
      exact_mod_cast this
    have ha : (badA p b).ncard = 0 := by omega
    have hb : (badB p b).ncard = 0 := by omega
    exact ⟨(Set.ncard_eq_zero (bad_finite p b).1).mp ha,
      (Set.ncard_eq_zero (bad_finite p b).2.1).mp hb⟩
  · rintro ⟨ha, hb⟩
    refine ⟨total p b (L p b), fun l hl => ?_⟩
    rw [residue_count p b l hl]
    have hs : slope p b = 0 := by unfold Plan.slope; simp [ha, hb]
    have := count_affine p b l hl
    rw [hs, zero_mul, add_zero] at this
    exact_mod_cast this

end Plan

-- PROOF.md 242-264. Signature copied character for character from Challenge.lean.
theorem trace_residue_eventually_affine_dev (k : ℕ) (hk : 2 ≤ k) (r : Fin (k + 1) → ℤ) (w n : ℤ) (hr0 : r 0 = 0) (hr : StrictMono r) (hw : r (Fin.last k) = w) (hn : 0 < n) (hnd : Int.gcd n (Finset.univ.gcd fun i : Fin k => r i.succ) = 1) : ∃ A B L : ℤ, 0 ≤ A ∧ 0 ≤ L ∧ ∀ l : ℤ, L ≤ l → ∃ N : ℕ, traceResidue (shiftedSemigroup k r n w l : Set ℤ) = N ∧ (N : ℤ) = A * l + B := by
  let p : Plan.Data := ⟨k, by omega, r, w, n, hr0, hr, hw, hn, hnd⟩
  obtain ⟨b⟩ := Plan.conductor_exists p
  obtain ⟨h1, h2, h3⟩ := Plan.explicit_affine p b
  exact ⟨Plan.slope p b, _, Plan.L p b, h1, h2, h3⟩

end EventualAffineTraceResidue
