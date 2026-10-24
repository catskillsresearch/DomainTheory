module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_13
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_20
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_4
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise215
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

section
/-- Membership for `𝒪`: a neighbourhood is the master `Δ = univ` or the empty set. -/
def memO (X : Set (Fin 1)) : Prop := X = Set.univ ∨ X = ∅
end

section
theorem nestedOrDisjoint_O : NestedOrDisjoint memO := by
  rintro X Y (rfl | rfl) (rfl | rfl)
  · exact Or.inl subset_rfl
  · exact Or.inr (Or.inl (Set.empty_subset _))
  · exact Or.inl (Set.empty_subset _)
  · exact Or.inl subset_rfl
end

section
theorem subMaster_O : ∀ {X : Set (Fin 1)}, memO X → X ⊆ Set.univ := fun _ => Set.subset_univ _
end

section
/- concordance: source L861 EXERCISE 2.15 opens classified by maps -/
/-- **Exercise 2.15 — the one-token system `𝒪 = {Δ, ∅}`.** -/
def O : NeighborhoodSystem (Fin 1) :=
  NeighborhoodSystem.ofNestedOrDisjoint memO Set.univ Set.univ_nonempty
    (Or.inl rfl) nestedOrDisjoint_O subMaster_O
end

section
@[simp] theorem O_mem {X : Set (Fin 1)} : O.mem X ↔ memO X := Iff.rfl
end

section
@[simp] theorem O_master : O.master = (Set.univ : Set (Fin 1)) := rfl
end

section
theorem O_mem_empty : O.mem (∅ : Set (Fin 1)) := Or.inr rfl
end

section
/-- `𝒪` is closed under intersection (used to verify the relation of `openToMap`). -/
theorem O_inter_mem {Y Y' : Set (Fin 1)} (hY : O.mem Y) (hY' : O.mem Y') : O.mem (Y ∩ Y') := by
  rcases hY with rfl | rfl
  · rw [Set.univ_inter]; exact hY'
  · rw [Set.empty_inter]; exact O_mem_empty
end

section
/-- The bottom element `⊥ = ↑Δ = {Δ}` of `|𝒪|`. -/
def botElt : O.Element := O.bot
end

section
/-- `Y ∈ ⊥` iff `Y = Δ = univ`. -/
theorem mem_botElt {Y : Set (Fin 1)} : botElt.mem Y ↔ Y = (Set.univ : Set (Fin 1)) := by
  rw [botElt, O.mem_bot, O_master]
end

section
/-- The top element `⊤ = ↑∅` of `|𝒪|`. -/
def topElt : O.Element := O.principal O_mem_empty
end

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — the open set of an approximable map.** `mapToOpen f = {x ∣ f(x) = ⊤}`. -/
def mapToOpen (f : ApproximableMap V O) : Set V.Element := {x | f.toElementMap x = topElt}
end

section
/-- **The defining property of `⊤`.** An element `z` of `|𝒪|` is `⊤` iff it contains `∅`: `∅` is
the sharpest neighbourhood, so `∅ ∈ z` forces `z` to be the principal filter `↑∅ = ⊤`. -/
theorem mem_empty_iff_eq_top (z : O.Element) : z.mem ∅ ↔ z = topElt := by
  constructor
  · intro hz
    exact O.eq_principal_of_isMin z hz (fun Y _ => Set.empty_subset Y)
  · rintro rfl
    exact ⟨O_mem_empty, subset_rfl⟩
end

section
/-- **Two elements.** Every element of `|𝒪|` is `⊥` or `⊤`. -/
theorem element_eq_bot_or_top (z : O.Element) : z = botElt ∨ z = topElt := by
  by_cases hz : z.mem ∅
  · exact Or.inr ((mem_empty_iff_eq_top z).mp hz)
  · refine Or.inl ?_
    apply Element.ext
    intro Y
    constructor
    · intro hY
      rcases (O_mem.mp (z.sub hY)) with rfl | rfl
      · exact mem_botElt.mpr rfl
      · exact absurd hY hz
    · intro hY
      rw [mem_botElt.mp hY, ← O_master]
      exact z.master_mem
end

section
/-- **Extensionality for `|𝒪|`.** Two elements agreeing on membership of `∅` are equal (it
distinguishes `⊥` from `⊤`). -/
theorem O_ext {z w : O.Element} (h : z.mem ∅ ↔ w.mem ∅) : z = w := by
  by_cases hz : z.mem ∅
  · rw [(mem_empty_iff_eq_top z).mp hz, (mem_empty_iff_eq_top w).mp (h.mp hz)]
  · have ez : z = botElt :=
      (element_eq_bot_or_top z).resolve_right (fun c => hz ((mem_empty_iff_eq_top z).mpr c))
    have ew : w = botElt :=
      (element_eq_bot_or_top w).resolve_right
        (fun c => (fun c' => hz (h.mpr c')) ((mem_empty_iff_eq_top w).mpr c))
    rw [ez, ew]
end

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- `mapToOpen f` is open: it is the preimage of the open point `{⊤} = [∅]` under the continuous
`x ↦ f(x)` (Exercise 2.13). -/
theorem isOpen_mapToOpen (f : ApproximableMap V O) : IsOpen (mapToOpen V f) := by
  have heq : mapToOpen V f = (fun x => f.toElementMap x) ⁻¹' O.basicOpen ∅ := by
    ext x
    simp only [mapToOpen, Set.mem_ofPred_eq, Set.mem_preimage, mem_basicOpen]
    exact (mem_empty_iff_eq_top (f.toElementMap x)).symm
  rw [heq]
  exact (O.isOpen_basicOpen ∅).preimage f.continuous_toElementMap
end

section
theorem univ_ne_empty : (Set.univ : Set (Fin 1)) ≠ ∅ := by
  intro h
  have h0 : (0 : Fin 1) ∈ (∅ : Set (Fin 1)) := h ▸ Set.mem_univ 0
  simp at h0
end

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — the approximable map of an open set.** For open `U ⊆ |𝒟|`, the relation
`X f Y ↔ X ∈ 𝒟 ∧ Y ∈ 𝒪 ∧ (Y = ∅ → ↑X ∈ U)`. The single nontrivial obligation is monotonicity:
sharpening the input `X' ⊆ X` means `↑X ⊑ ↑X'`, and `U` open (an upper set) carries `↑X ∈ U` up to
`↑X' ∈ U`. Choice-free. -/
def openToMap (U : Set V.Element) (hU : IsOpen U) : ApproximableMap V O where
  rel X Y := V.mem X ∧ O.mem Y ∧ (Y = ∅ → ∃ hX : V.mem X, V.principal hX ∈ U)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V.master_mem, O.master_mem, fun heq => (univ_ne_empty (O_master ▸ heq)).elim⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, fY⟩ ⟨_, hY', fY'⟩
    refine ⟨hX, O_inter_mem hY hY', ?_⟩
    intro h
    rcases O_mem.mp hY with rfl | rfl
    · rw [Set.univ_inter] at h; exact fY' h
    · exact fY rfl
  mono := by
    rintro X X' Y Y' ⟨hX, _, fY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', hY', ?_⟩
    intro hY'eq
    have hYeq : Y = ∅ := Set.subset_empty_iff.mp (hY'eq ▸ hYY')
    obtain ⟨hX0, hmem⟩ := fY hYeq
    have hmem' : V.principal hX ∈ U := hmem
    have hle : V.principal hX ≤ V.principal hX' := (V.principal_le_iff hX hX').mpr hX'X
    exact ⟨hX', V.isOpen_isUpperSet hU hmem' hle⟩
end

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- The value of `openToMap U hU` on the finite element `↑X` contains `∅` iff `↑X ∈ U`; i.e.
`(openToMap U hU)(↑X) = ⊤ ↔ ↑X ∈ U`. -/
theorem toElementMap_openToMap_principal_mem_empty (U : Set V.Element) (hU : IsOpen U)
    {X : Set γ} (hX : V.mem X) :
    ((openToMap V U hU).toElementMap (V.principal hX)).mem ∅ ↔ V.principal hX ∈ U := by
  rw [← (openToMap V U hU).rel_iff_mem_principal hX]
  constructor
  · rintro ⟨_, _, fimpl⟩
    obtain ⟨_, hmem⟩ := fimpl rfl
    exact hmem
  · intro h
    exact ⟨hX, O_mem_empty, fun _ => ⟨hX, h⟩⟩
end

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — round trip (open → map → open).** `mapToOpen (openToMap U hU) = U`. -/
theorem mem_mapToOpen_openToMap (U : Set V.Element) (hU : IsOpen U) (x : V.Element) :
    x ∈ mapToOpen V (openToMap V U hU) ↔ x ∈ U := by
  rw [mapToOpen, Set.mem_ofPred_eq, ← mem_empty_iff_eq_top,
    ApproximableMap.toElementMap_mem_iff_principal]
  constructor
  · rintro ⟨X, hxX, hmem⟩
    rw [toElementMap_openToMap_principal_mem_empty] at hmem
    have hple : V.principal (x.sub hxX) ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    exact V.isOpen_isUpperSet hU hmem hple
  · intro hxU
    obtain ⟨X, hxX, hXU⟩ := hU.out x hxU
    refine ⟨X, hxX, ?_⟩
    rw [toElementMap_openToMap_principal_mem_empty]
    exact hXU (show V.principal (x.sub hxX) ∈ V.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)
end

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — round trip (map → open → map).** `openToMap (mapToOpen f) = f`. -/
theorem openToMap_mapToOpen (f : ApproximableMap V O) :
    openToMap V (mapToOpen V f) (isOpen_mapToOpen V f) = f := by
  apply ApproximableMap.eq_of_toElementMap_principal
  intro X hX
  apply O_ext
  rw [toElementMap_openToMap_principal_mem_empty, mapToOpen, Set.mem_ofPred_eq,
    ← mem_empty_iff_eq_top]
end

section
set_option linter.unusedVariables false

theorem example_215.{u_1} : And
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
    (hU :
      @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement γ V) U)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V),
    Iff
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V
          (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V U hU))
        x)
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)) U x))
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (f :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O)
      (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V f)
        (@DomainTheory.NeighbourhoodSystems.Exercise215.isOpen_mapToOpen γ V f))
      f) :=
  @And.intro
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
    (hU :
      @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement γ V) U)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V),
    Iff
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V
          (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V U hU))
        x)
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)) U x))
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (f :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O)
      (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V f)
        (@DomainTheory.NeighbourhoodSystems.Exercise215.isOpen_mapToOpen γ V f))
      f)
  @DomainTheory.NeighbourhoodSystems.Exercise215.mem_mapToOpen_openToMap
  @DomainTheory.NeighbourhoodSystems.Exercise215.openToMap_mapToOpen
end

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 (main).** The open subsets of `|𝒟|` are in one-one correspondence with the
approximable mappings `𝒟 → 𝒪`, via `U ↦ openToMap U` and `f ↦ {x ∣ f(x) = ⊤}`. -/
def openSet_equiv_map : {U : Set V.Element // IsOpen U} ≃ ApproximableMap V O where
  toFun U := openToMap V U.1 U.2
  invFun f := ⟨mapToOpen V f, isOpen_mapToOpen V f⟩
  left_inv := by
    rintro ⟨U, hU⟩
    apply Subtype.ext
    ext x
    exact mem_mapToOpen_openToMap V U hU x
  right_inv f := openToMap_mapToOpen V f
end

section
theorem O_mem_univ : O.mem (Set.univ : Set (Fin 1)) := Or.inl rfl
end

section
/-- The open point `{⊤}` is the basic open `[∅]`. -/
theorem basicOpen_empty_eq_singleton_top : O.basicOpen ∅ = {topElt} := by
  ext x
  rw [mem_basicOpen, mem_empty_iff_eq_top]
  exact Set.mem_singleton_iff.symm
end

section
/-- `⊥ ⊑ ⊤`. -/
theorem botElt_le_topElt : botElt ≤ topElt := O.bot_le _
end

section
/-- `⊥ ≠ ⊤` (so `⊥ ⊏ ⊤`). -/
theorem botElt_ne_topElt : botElt ≠ topElt := by
  intro h
  have htop : topElt.mem ∅ := ⟨O_mem_empty, subset_rfl⟩
  rw [← h, mem_botElt] at htop
  exact univ_ne_empty htop.symm
end

section
/-- **The opens of `|𝒪|`.** `{⊥}` is not open: `⊥` is the generic point. (The basic neighbourhood of
`⊥` is `[Δ] = |𝒪|`, which is not contained in `{⊥}` because it also contains `⊤`.) -/
theorem not_isOpen_singleton_botElt : ¬ IsOpen ({botElt} : Set O.Element) := by
  intro h
  obtain ⟨X, hX, hsub⟩ := h.out botElt rfl
  rw [mem_botElt] at hX
  subst hX
  have htop : topElt ∈ ({botElt} : Set O.Element) :=
    hsub (show topElt ∈ O.basicOpen Set.univ from (O_master ▸ topElt.master_mem))
  exact botElt_ne_topElt (Set.mem_singleton_iff.mp htop).symm
end

end DomainTheory.NeighbourhoodSystems.Exercise215
