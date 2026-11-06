module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_11
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_10

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_19

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*}

def unionMap (V : NeighborhoodSystem α) :
    ApproximableMap V.PowerDomain.PowerDomain V.PowerDomain where
  rel A B := V.PowerDomain.PDmem A ∧ V.PDmem B ∧ ∀ S ∈ A, ∀ X ∈ S, ∃ Y ∈ B, X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨V.PowerDomain.PDmem_master, V.PDmem_master, ?_⟩
    intro S hS X hX
    simp only [mem_upSet] at hS
    exact ⟨V.master, ⟨V.master_mem, subset_rfl⟩, V.sub_master (V.PDmem_mem hS.1 hX)⟩
  inter_right := by
    rintro A B B' ⟨hA, hB, hbody⟩ ⟨-, hB', hbody'⟩
    refine ⟨hA, V.PDmem_inter hB hB', ?_⟩
    intro S hS X hX
    obtain ⟨Y, hYB, hXY⟩ := hbody S hS X hX
    obtain ⟨Y', hY'B', hXY'⟩ := hbody' S hS X hX
    have hXmem : V.mem X := V.PDmem_mem (V.PowerDomain.PDmem_mem hA hS) hX
    have hYmem : V.mem Y := V.PDmem_mem hB hYB
    have hY'mem : V.mem Y' := V.PDmem_mem hB' hY'B'
    have hsub : X ⊆ Y ∩ Y' := Set.subset_inter hXY hXY'
    have hinmem : V.mem (Y ∩ Y') := V.inter_mem hYmem hY'mem hXmem hsub
    exact ⟨Y ∩ Y', Set.mem_inter
      (V.PDmem_down hB hYB Set.inter_subset_left hinmem)
      (V.PDmem_down hB' hY'B' Set.inter_subset_right hinmem), hsub⟩
  mono := by
    rintro A A' B B' ⟨_, _, hbody⟩ hA'A hBB' hA' hB'
    refine ⟨hA', hB', ?_⟩
    intro S hS X hX
    obtain ⟨Y, hYB, hXY⟩ := hbody S (hA'A hS) X hX
    exact ⟨Y, hBB' hYB, hXY⟩

@[simp] theorem unionMap_rel {V : NeighborhoodSystem α} {A : Set (Set (Set α))} {B : Set (Set α)} :
    (unionMap V).rel A B ↔ V.PowerDomain.PDmem A ∧ V.PDmem B ∧ ∀ S ∈ A, ∀ X ∈ S, ∃ Y ∈ B, X ⊆ Y :=
  Iff.rfl

theorem unionMap_rel_Ypd_iff {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    (Q : ComputablePresentation V.PowerDomain) (hQ : ∀ c, Q.X c = V.Ypd P c) {n m : ℕ} :
    (unionMap V).rel (V.PowerDomain.Ypd Q n) (V.Ypd P m)
      ↔ ∀ c ∈ decodeList n, ∀ a ∈ decodeList c, ∃ b ∈ decodeList m, P.X a ⊆ P.X b := by
  constructor
  · rintro ⟨-, -, hbody⟩ c hc a ha
    have hSmem : Q.X c ∈ V.PowerDomain.Ypd Q n :=
      (V.PowerDomain.mem_Ypd Q).mpr ⟨c, hc, Q.mem_X c, subset_rfl⟩
    have hXinS : P.X a ∈ Q.X c := by
      rw [hQ c]; exact (V.mem_Ypd P).mpr ⟨a, ha, P.mem_X a, subset_rfl⟩
    obtain ⟨Y, hYB, hXY⟩ := hbody (Q.X c) hSmem (P.X a) hXinS
    obtain ⟨b, hb, hYin⟩ := (V.mem_Ypd P).mp hYB
    exact ⟨b, hb, hXY.trans hYin.2⟩
  · intro hgen
    refine ⟨V.PowerDomain.Ypd_isPDmem Q n, V.Ypd_isPDmem P m, ?_⟩
    intro S hS X hX
    obtain ⟨c, hc, hScod⟩ := (V.PowerDomain.mem_Ypd Q).mp hS
    have hXinQ : X ∈ Q.X c := hScod.2 hX
    rw [hQ c] at hXinQ
    obtain ⟨a, ha, hXin⟩ := (V.mem_Ypd P).mp hXinQ
    obtain ⟨b, hb, hab⟩ := hgen c hc a ha
    exact ⟨P.X b, (V.mem_Ypd P).mpr ⟨b, hb, P.mem_X b, subset_rfl⟩, hXin.2.trans hab⟩

theorem ypd_zero_subset_inter {V : NeighborhoodSystem α} (P : ComputablePresentation V) (a b : ℕ) :
    V.Ypd P 0 ⊆ V.Ypd P a ∩ V.Ypd P b := by
  rw [V.Ypd_zero P]
  exact Set.empty_subset _

theorem unionMap_isComputable {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    (consV : ℕ → ℕ) (hconsVp : Nat.Primrec consV)
    (hconsVs : ∀ a b, consV (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ComputableMap
      (V.PowerDomain.PDPresentation (V.PDPresentation P consV hconsVp hconsVs)
        (fun _ => 1) (Nat.Primrec.const 1)
        (fun a b => ⟨fun _ => ⟨0, ypd_zero_subset_inter P a b⟩, fun _ => rfl⟩))
      (V.PDPresentation P consV hconsVp hconsVs)
      (unionMap V) := by
  constructor
  have hrd : RecDecidable₂ (fun n m => ∀ c ∈ decodeList n, ∀ a ∈ decodeList c,
      ∃ b ∈ decodeList m, P.X a ⊆ P.X b) := (V.subCode_computable P).bForallList
  have key : RecDecidable₂ (fun n m => (unionMap V).rel
      (V.PowerDomain.Ypd (V.PDPresentation P consV hconsVp hconsVs) n) (V.Ypd P m)) := by
    refine RecDecidable.of_iff (fun t => ?_) hrd
    exact unionMap_rel_Ypd_iff P (V.PDPresentation P consV hconsVp hconsVs) (fun _ => rfl)
  exact key.re

theorem unionMap_rel_fin (V : NeighborhoodSystem α) {LS : List (List (Set α))} {LY : List (Set α)}
    (hLS : ∀ l ∈ LS, ∀ X ∈ l, V.mem X) (hLY : ∀ Y ∈ LY, V.mem Y) :
    (unionMap V).rel (⋃ l ∈ LS, V.PowerDomain.upSet (⋃ X ∈ l, V.upSet X)) (⋃ Y ∈ LY, V.upSet Y)
      ↔ ∀ l ∈ LS, ∀ X ∈ l, ∃ Y ∈ LY, X ⊆ Y := by
  constructor
  · rintro ⟨-, -, hbody⟩ l hl X hX
    have hXmem : V.mem X := hLS l hl X hX
    have hSinA : (⋃ X ∈ l, V.upSet X) ∈ ⋃ l ∈ LS, V.PowerDomain.upSet (⋃ X ∈ l, V.upSet X) :=
      Set.mem_iUnion₂.mpr ⟨l, hl, (⟨l, hLS l hl, rfl⟩ : V.PDmem _), subset_rfl⟩
    have hXinS : X ∈ ⋃ X' ∈ l, V.upSet X' := (V.mem_PDunion).mpr ⟨X, hX, hXmem, subset_rfl⟩
    obtain ⟨Y, hYB, hXY⟩ := hbody _ hSinA X hXinS
    obtain ⟨Y', hY', hYin⟩ := (V.mem_PDunion).mp hYB
    exact ⟨Y', hY', hXY.trans hYin.2⟩
  · intro hgen
    refine ⟨?_, ⟨LY, hLY, rfl⟩, ?_⟩
    · refine ⟨LS.map (fun l => ⋃ X ∈ l, V.upSet X), ?_, ?_⟩
      · intro S hS
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hS
        exact ⟨l, hLS l hl, rfl⟩
      · ext z
        simp only [Set.mem_iUnion, List.mem_map, exists_prop]
        constructor
        · rintro ⟨l, hl, hz⟩
          exact ⟨_, ⟨l, hl, rfl⟩, hz⟩
        · rintro ⟨S, ⟨l, hl, rfl⟩, hz⟩
          exact ⟨l, hl, hz⟩
    · intro S hS X hX
      obtain ⟨l, hl, hSin⟩ := Set.mem_iUnion₂.mp hS
      have hXin : X ∈ ⋃ X' ∈ l, V.upSet X' := hSin.2 hX
      obtain ⟨X', hX', hXmem⟩ := (V.mem_PDunion).mp hXin
      obtain ⟨Y, hY, hX'Y⟩ := hgen l hl X' hX'
      exact ⟨Y, (V.mem_PDunion).mpr ⟨Y, hY, hLY Y hY, subset_rfl⟩, hXmem.2.trans hX'Y⟩

end

section
set_option linter.unusedVariables false
open NeighborhoodSystem Domain.Recursive ApproximableMap

/-- Scott's Exercise 7.20: union map on the powerdomain is computable. -/
theorem example_720 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
      (consV : ℕ → ℕ) (hconsVp : Nat.Primrec consV)
      (hconsVs : ∀ a b, consV (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b),
      ComputableMap
        (V.PowerDomain.PDPresentation (V.PDPresentation P consV hconsVp hconsVs)
          (fun _ => 1) (Nat.Primrec.const 1)
          (fun a b => ⟨fun _ => ⟨0, ypd_zero_subset_inter P a b⟩, fun _ => rfl⟩))
        (V.PDPresentation P consV hconsVp hconsVs) (unionMap V)) ∧
    (∀ {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
      (Q : ComputablePresentation V.PowerDomain) (hQ : ∀ c, Q.X c = V.Ypd P c) {n m : ℕ},
      (unionMap V).rel (V.PowerDomain.Ypd Q n) (V.Ypd P m) ↔
        ∀ c ∈ decodeList n, ∀ a ∈ decodeList c, ∃ b ∈ decodeList m, P.X a ⊆ P.X b) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) {LS : List (List (Set α))} {LY : List (Set α)}
      (hLS : ∀ l ∈ LS, ∀ X ∈ l, V.mem X) (hLY : ∀ Y ∈ LY, V.mem Y),
      (unionMap V).rel (⋃ l ∈ LS, V.PowerDomain.upSet (⋃ X ∈ l, V.upSet X))
        (⋃ Y ∈ LY, V.upSet Y) ↔ ∀ l ∈ LS, ∀ X ∈ l, ∃ Y ∈ LY, X ⊆ Y) :=
  ⟨@unionMap_isComputable, ⟨@unionMap_rel_Ypd_iff, @unionMap_rel_fin⟩⟩
end


end DomainTheory.NeighbourhoodSystems
end
