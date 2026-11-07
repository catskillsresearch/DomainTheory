module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_12
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_15
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.regularCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.regularLanguage

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}

structure EffectiveIso {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) where
  toMap : ApproximableMap V W
  invMap : ApproximableMap W V
  toMap_computable : ComputableMap P Q toMap
  invMap_computable : ComputableMap Q P invMap
  left_inv : invMap.comp toMap = idMap V
  right_inv : toMap.comp invMap = idMap W

def EffectivelyIsomorphic {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) : Prop :=
  Nonempty (EffectiveIso P Q)
end

namespace EffectiveIso

def fiber2 (S : Set (ℕ × (ℕ × α))) (i j : ℕ) : Set α := fiber (fiber S i) j

@[simp] theorem mem_fiber2 {S : Set (ℕ × (ℕ × α))} {i j : ℕ} {a : α} :
    a ∈ fiber2 S i j ↔ (i, (j, a)) ∈ S := Iff.rfl

theorem fiber2_inter (S S' : Set (ℕ × (ℕ × α))) (i j : ℕ) :
    fiber2 (S ∩ S') i j = fiber2 S i j ∩ fiber2 S' i j := rfl

theorem fiber2_master (i j : ℕ) :
    fiber2 ((iterSys (iterSys V)).master) i j = V.master := by
  show fiber (fiber ((iterSys (iterSys V)).master) i) j = V.master
  rw [fiber_iterSys_master, fiber_iterSys_master]

theorem fiber2_mono {S S' : Set (ℕ × (ℕ × α))} (h : S ⊆ S') (i j : ℕ) :
    fiber2 S i j ⊆ fiber2 S' i j := fun _ ha => h ha

theorem mem_fiber2_of_mem {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) (i j : ℕ) :
    V.mem (fiber2 S i j) := (hS.1 i).1 j

end EffectiveIso

namespace EffectiveIso
open NeighborhoodSystem Domain.Recursive ApproximableMap

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}

def reindexF (W : Set (ℕ × α)) : Set (ℕ × (ℕ × α)) :=
  {p | p.2.2 ∈ fiber W (Nat.pair p.1 p.2.1)}

@[simp] theorem fiber2_reindexF (W : Set (ℕ × α)) (i j : ℕ) :
    fiber2 (reindexF W) i j = fiber W (Nat.pair i j) := rfl

def reindexG (S : Set (ℕ × (ℕ × α))) : Set (ℕ × α) :=
  {p | p.2 ∈ fiber2 S (Nat.unpair p.1).1 (Nat.unpair p.1).2}

@[simp] theorem fiber_reindexG (S : Set (ℕ × (ℕ × α))) (k : ℕ) :
    fiber (reindexG S) k = fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 := rfl

theorem exists_inner_bound {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) :
    ∀ n, ∃ M, ∀ i, i < n → ∀ j, M ≤ j → fiber2 S i j = V.master := by
  intro n
  induction n with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨Mn, hMn⟩ := (hS.1 n).2
    refine ⟨max M Mn, fun i hi j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact hM i hlt j (le_trans (le_max_left _ _) hj)
    · subst heq
      exact hMn j (le_trans (le_max_right _ _) hj)

theorem pair_lt_pair_of_lt {x y i j : ℕ} (hx : x < i) (hy : y < j) :
    Nat.pair x y < Nat.pair i j := by
  have hms : ∀ z : ℕ, (z + 1) * (z + 1) = z * z + 2 * z + 1 := fun z => by
    rw [Nat.succ_mul, Nat.mul_succ]; omega
  have hlt : Nat.pair x y < (max x y + 1) * (max x y + 1) := by
    unfold Nat.pair
    rcases lt_or_ge x y with h | h
    · rw [ite_eq_left h, show max x y = y by omega, hms]; omega
    · rw [ite_eq_right (by omega), show max x y = x by omega, hms]; omega
  have hle : max i j * max i j ≤ Nat.pair i j := by
    unfold Nat.pair
    rcases lt_or_ge i j with h | h
    · rw [ite_eq_left h, show max i j = j by omega]; omega
    · rw [ite_eq_right (by omega), show max i j = i by omega]; omega
  have h3 : max x y + 1 ≤ max i j := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; have := le_max_right i j; omega
    · rw [max_eq_left h]; have := le_max_left i j; omega
  have h4 : (max x y + 1) * (max x y + 1) ≤ max i j * max i j := Nat.mul_le_mul h3 h3
  omega

theorem reindexF_mem {W : Set (ℕ × α)} (hW : (iterSys V).mem W) :
    (iterSys (iterSys V)).mem (reindexF W) := by
  obtain ⟨hWf, Nw, hNw⟩ := hW
  refine ⟨fun i => ⟨fun j => ?_, Nw, fun j hj => ?_⟩, Nw, fun i hi => ?_⟩
  ·
    show V.mem (fiber2 (reindexF W) i j)
    rw [fiber2_reindexF]; exact hWf (Nat.pair i j)
  ·
    show fiber2 (reindexF W) i j = V.master
    rw [fiber2_reindexF]
    exact hNw (Nat.pair i j) (le_trans hj (le_pair_right i j))
  ·
    apply eq_of_fiber_eq
    intro j
    show fiber2 (reindexF W) i j = fiber ((iterSys V).master) j
    rw [fiber2_reindexF, fiber_iterSys_master]
    exact hNw (Nat.pair i j) (le_trans hi (le_pair_left i j))

theorem reindexF_subset_iff {W : Set (ℕ × α)} {S : Set (ℕ × (ℕ × α))} :
    reindexF W ⊆ S ↔ ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j := by
  constructor
  · intro h i j
    have := fiber2_mono h i j
    rwa [fiber2_reindexF] at this
  · intro h
    refine subset_of_fiber_subset (fun i => subset_of_fiber_subset (fun j => ?_))
    show fiber2 (reindexF W) i j ⊆ fiber2 S i j
    rw [fiber2_reindexF]; exact h i j

def Fmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys V) (iterSys (iterSys V)) where
  rel W S := (iterSys V).mem W ∧ (iterSys (iterSys V)).mem S ∧
    ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys V).master_mem, (iterSys (iterSys V)).master_mem, fun i j => by
    rw [fiber_iterSys_master, fiber2_master]⟩
  inter_right := by
    rintro W S S' ⟨hW, hS, hf⟩ ⟨-, hS', hf'⟩
    refine ⟨hW, (iterSys (iterSys V)).inter_mem hS hS' (reindexF_mem hW) ?_, fun i j => ?_⟩
    · exact Set.subset_inter (reindexF_subset_iff.mpr hf) (reindexF_subset_iff.mpr hf')
    · rw [fiber2_inter]; exact Set.subset_inter (hf i j) (hf' i j)
  mono := by
    rintro W W' S S' ⟨hW, hS, hf⟩ hW'W hSS' hW' hS'
    exact ⟨hW', hS', fun i j => ((fiber_mono hW'W _).trans (hf i j)).trans (fiber2_mono hSS' i j)⟩

@[simp] theorem Fmap_rel {W : Set (ℕ × α)} {S : Set (ℕ × (ℕ × α))} :
    (Fmap V).rel W S ↔ (iterSys V).mem W ∧ (iterSys (iterSys V)).mem S ∧
      ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j := Iff.rfl

theorem reindexG_mem {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) :
    (iterSys V).mem (reindexG S) := by
  obtain ⟨No, hNo⟩ := hS.2
  obtain ⟨M, hM⟩ := exists_inner_bound hS No
  refine ⟨fun k => ?_, Nat.pair No M, fun k hk => ?_⟩
  ·
    rw [fiber_reindexG]; exact mem_fiber2_of_mem hS _ _
  ·
    rw [fiber_reindexG]
    set i := (Nat.unpair k).1 with hi
    set j := (Nat.unpair k).2 with hj
    by_cases hiN : i < No
    · by_cases hjM : j < M
      · exfalso
        have hklt : Nat.pair i j < Nat.pair No M := pair_lt_pair_of_lt hiN hjM
        rw [pair_unpair] at hklt
        omega
      · exact hM i hiN j (not_lt.mp hjM)
    · have h1 : fiber S i = (iterSys V).master := hNo i (not_lt.mp hiN)
      show fiber2 S i j = V.master
      rw [fiber2, h1, fiber_iterSys_master]

theorem reindexG_subset_iff {S : Set (ℕ × (ℕ × α))} {W : Set (ℕ × α)} :
    reindexG S ⊆ W ↔ ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k := by
  constructor
  · intro h k
    have := fiber_mono h k
    rwa [fiber_reindexG] at this
  · intro h
    refine subset_of_fiber_subset (fun k => ?_)
    rw [fiber_reindexG]; exact h k

def Gmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys (iterSys V)) (iterSys V) where
  rel S W := (iterSys (iterSys V)).mem S ∧ (iterSys V).mem W ∧
    ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys (iterSys V)).master_mem, (iterSys V).master_mem, fun k => by
    rw [fiber2_master, fiber_iterSys_master]⟩
  inter_right := by
    rintro S W W' ⟨hS, hW, hg⟩ ⟨-, hW', hg'⟩
    refine ⟨hS, (iterSys V).inter_mem hW hW' (reindexG_mem hS) ?_, fun k => ?_⟩
    · exact Set.subset_inter (reindexG_subset_iff.mpr hg) (reindexG_subset_iff.mpr hg')
    · rw [fiber_inter]; exact Set.subset_inter (hg k) (hg' k)
  mono := by
    rintro S S' W W' ⟨hS, hW, hg⟩ hS'S hWW' hS' hW'
    exact ⟨hS', hW', fun k => ((fiber2_mono hS'S _ _).trans (hg k)).trans (fiber_mono hWW' k)⟩

@[simp] theorem Gmap_rel {S : Set (ℕ × (ℕ × α))} {W : Set (ℕ × α)} :
    (Gmap V).rel S W ↔ (iterSys (iterSys V)).mem S ∧ (iterSys V).mem W ∧
      ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k := Iff.rfl

theorem Fmap_comp_Gmap : (Fmap V).comp (Gmap V) = idMap (iterSys (iterSys V)) := by
  apply ApproximableMap.ext
  intro S S'
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hS, hW, hg⟩, ⟨-, hS', hf⟩⟩
    refine ⟨hS, hS', subset_of_fiber_subset (fun i => subset_of_fiber_subset (fun j => ?_))⟩
    show fiber2 S i j ⊆ fiber2 S' i j
    have h1 : fiber2 S i j ⊆ fiber W (Nat.pair i j) := by
      have := hg (Nat.pair i j)
      rwa [unpair_pair_fst, unpair_pair_snd] at this
    exact h1.trans (hf i j)
  · rintro ⟨hS, hS', hSS'⟩
    refine ⟨reindexG S, ⟨hS, reindexG_mem hS, ?_⟩, ⟨reindexG_mem hS, hS', ?_⟩⟩
    · intro k; rw [fiber_reindexG]
    · intro i j
      rw [fiber_reindexG, unpair_pair_fst, unpair_pair_snd]
      exact fiber2_mono hSS' i j

theorem Gmap_comp_Fmap : (Gmap V).comp (Fmap V) = idMap (iterSys V) := by
  apply ApproximableMap.ext
  intro W W'
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨S, ⟨hW, hS, hf⟩, ⟨-, hW', hg⟩⟩
    refine ⟨hW, hW', subset_of_fiber_subset (fun k => ?_)⟩
    have h1 : fiber W k ⊆ fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 := by
      have := hf (Nat.unpair k).1 (Nat.unpair k).2
      rwa [pair_unpair] at this
    exact h1.trans (hg k)
  · rintro ⟨hW, hW', hWW'⟩
    refine ⟨reindexF W, ⟨hW, reindexF_mem hW, ?_⟩, ⟨reindexF_mem hW, hW', ?_⟩⟩
    · intro i j; rw [fiber2_reindexF]
    · intro k
      rw [fiber2_reindexF, pair_unpair]
      exact fiber_mono hWW' k

end

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)

theorem fiber2_iterEnum_iter (m i j : ℕ) :
    fiber2 (iterEnum (iterPresentation P) m) i j
      = P.X (iterIdx P (iterIdx (iterPresentation P) m i) j) := by
  show fiber (fiber (iterEnum (iterPresentation P) m) i) j = _
  rw [fiber_iterEnum, iterPresentation_X, fiber_iterEnum]
end

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)
variable {P}

theorem Gmap_rel_enum_iff (s n : ℕ) :
    (Gmap V).rel (iterEnum (iterPresentation P) s) (iterEnum P n) ↔
      ∀ k, k < n →
        P.X (iterIdx P (iterIdx (iterPresentation P) s (Nat.unpair k).1) (Nat.unpair k).2)
          ⊆ P.X (iterIdx P n k) := by
  rw [Gmap_rel]
  have hmem₁ := iterEnum_mem (P := iterPresentation P) s
  have hmem₂ := iterEnum_mem (P := P) n
  constructor
  · rintro ⟨-, -, hg⟩ k _
    have := hg k
    rwa [fiber2_iterEnum_iter, fiber_iterEnum] at this
  · intro hbd
    refine ⟨hmem₁, hmem₂, fun k => ?_⟩
    rw [fiber2_iterEnum_iter, fiber_iterEnum]
    by_cases hk : k < n
    · exact hbd k hk
    · rw [iterIdx_ge (not_lt.mp hk), P.masterIdx_spec]
      exact V.sub_master (P.mem_X _)

theorem Gmap_isComputable :
    ComputableMap (iterPresentation (iterPresentation P)) (iterPresentation P) (Gmap V) := by
  constructor

  have hLHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1)
        u.unpair.1.unpair.2) := by
    have hinner : Nat.Primrec (fun u : ℕ =>
        iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1) := by
      refine (primrec_nthCode.comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair
          ((Nat.Primrec.left.comp Nat.Primrec.left).pair
            (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq (fun u => ?_)
      simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
    refine (primrec_nthCode.comp
      (hinner.pair ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P u.unpair.2.unpair.2 u.unpair.1) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.right.comp Nat.Primrec.right).pair
        (Nat.Primrec.left.pair (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hp₂ : RecDecidable (fun u : ℕ =>
      P.X (iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1)
        u.unpair.1.unpair.2) ⊆ P.X (iterIdx P u.unpair.2.unpair.2 u.unpair.1)) := by
    refine RecDecidable.of_iff (fun u => ?_) (P.incl_computable.comp (hLHS.pair hRHS))
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hbound₁ : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hp₀ := hp₂.bForall hbound₁
  refine (RecDecidable.of_iff (fun t => ?_) hp₀).re
  simp only [iterPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact Gmap_rel_enum_iff t.unpair.1 t.unpair.2

end

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)

theorem masterIdx_iterPresentation : (iterPresentation P).masterIdx = 0 := rfl
end

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)
variable {P}

theorem Fmap_rel_enum_iff (n m : ℕ) :
    (Fmap V).rel (iterEnum P n) (iterEnum (iterPresentation P) m) ↔
      ∀ i, i < m → ∀ j, j < iterIdx (iterPresentation P) m i →
        P.X (iterIdx P n (Nat.pair i j)) ⊆ P.X (iterIdx P (iterIdx (iterPresentation P) m i) j) := by
  rw [Fmap_rel]
  have hmem₁ := iterEnum_mem (P := P) n
  have hmem₂ := iterEnum_mem (P := iterPresentation P) m
  constructor
  · rintro ⟨-, -, hf⟩ i _ j _
    have := hf i j
    rwa [fiber_iterEnum, fiber2_iterEnum_iter] at this
  · intro hbd
    refine ⟨hmem₁, hmem₂, fun i j => ?_⟩
    rw [fiber_iterEnum, fiber2_iterEnum_iter]
    by_cases hi : i < m
    · by_cases hj : j < iterIdx (iterPresentation P) m i
      · exact hbd i hi j hj
      ·
        rw [iterIdx_ge (not_lt.mp hj), P.masterIdx_spec]
        exact V.sub_master (P.mem_X _)
    ·
      have h0 : iterIdx (iterPresentation P) m i = 0 := by
        rw [iterIdx_ge (not_lt.mp hi), masterIdx_iterPresentation]
      rw [h0, iterIdx_ge (Nat.zero_le j), P.masterIdx_spec]
      exact V.sub_master (P.mem_X _)

theorem Fmap_isComputable :
    ComputableMap (iterPresentation P) (iterPresentation (iterPresentation P)) (Fmap V) := by
  constructor

  have hLHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P u.unpair.2.unpair.2.unpair.1 (Nat.pair u.unpair.2.unpair.1 u.unpair.1)) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left).pair
          (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1)
        u.unpair.1) := by
    have hinner : Nat.Primrec (fun u : ℕ =>
        iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1) := by
      refine (primrec_nthCode.comp
        ((Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
          ((Nat.Primrec.left.comp Nat.Primrec.right).pair
            (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq (fun u => ?_)
      simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
    refine (primrec_nthCode.comp
      (hinner.pair (Nat.Primrec.left.pair (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hp₂ : RecDecidable (fun u : ℕ =>
      P.X (iterIdx P u.unpair.2.unpair.2.unpair.1 (Nat.pair u.unpair.2.unpair.1 u.unpair.1))
        ⊆ P.X (iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2
          u.unpair.2.unpair.1) u.unpair.1)) := by
    refine RecDecidable.of_iff (fun u => ?_) (P.incl_computable.comp (hLHS.pair hRHS))
    simp only [unpair_pair_fst, unpair_pair_snd]

  have hbound₂ : Nat.Primrec (fun v : ℕ =>
      iterIdx (iterPresentation P) v.unpair.2.unpair.2 v.unpair.1) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.right.comp Nat.Primrec.right).pair
        (Nat.Primrec.left.pair (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq
      (fun v => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hbound₁ : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hp₁ := hp₂.bForall hbound₂
  have hp₀ := hp₁.bForall hbound₁
  refine (RecDecidable.of_iff (fun t => ?_) hp₀).re

  simp only [iterPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact Fmap_rel_enum_iff t.unpair.1 t.unpair.2

def iterIterEffectiveIso (P : ComputablePresentation V) :
    EffectiveIso (iterPresentation P) (iterPresentation (iterPresentation P)) where
  toMap := Fmap V
  invMap := Gmap V
  toMap_computable := Fmap_isComputable
  invMap_computable := Gmap_isComputable
  left_inv := Gmap_comp_Fmap
  right_inv := Fmap_comp_Gmap

end

end EffectiveIso

namespace EffectiveIso
open NeighborhoodSystem Domain.Recursive ApproximableMap

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}

def toDomainIso (e : EffectiveIso P Q) : DomainIso V W where
  toFun := e.toMap.toElementMap
  invFun := e.invMap.toElementMap
  left_inv x := by
    rw [← toElementMap_comp, e.left_inv, toElementMap_idMap]
  right_inv y := by
    rw [← toElementMap_comp, e.right_inv, toElementMap_idMap]
  map_rel_iff' := by
    intro x y
    show e.toMap.toElementMap x ≤ e.toMap.toElementMap y ↔ x ≤ y
    refine ⟨fun h => ?_, fun h => e.toMap.toElementMap_mono h⟩
    have hmono := e.invMap.toElementMap_mono h
    rwa [← toElementMap_comp, ← toElementMap_comp, e.left_inv, toElementMap_idMap,
      toElementMap_idMap] at hmono

end
end EffectiveIso

section
variable {α β : Type*}

theorem EffectivelyIsomorphic.isomorphic {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {P : ComputablePresentation V} {Q : ComputablePresentation W}
    (h : EffectivelyIsomorphic P Q) : V ≅ᴰ W :=
  h.elim fun e => ⟨e.toDomainIso⟩

variable {V : NeighborhoodSystem α}

theorem iterSys_effectivelyIsomorphic_iterIter (P : ComputablePresentation V) :
    EffectivelyIsomorphic (iterPresentation P) (iterPresentation (iterPresentation P)) :=
  ⟨EffectiveIso.iterIterEffectiveIso P⟩

theorem iterSys_isomorphic_iterIter (P : ComputablePresentation V) :
    iterSys V ≅ᴰ iterSys (iterSys V) :=
  (iterSys_effectivelyIsomorphic_iterIter P).isomorphic
end

end DomainTheory.NeighbourhoodSystems
