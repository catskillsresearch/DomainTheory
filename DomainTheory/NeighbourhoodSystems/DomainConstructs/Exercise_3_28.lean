module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_27
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

def leastMapVals (L : List (Set α × Set β)) (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (x : V₀.Element) : Set V₁.Element :=
  {z | ∃ (p : Set α × Set β) (hp : p ∈ L), x.mem p.1 ∧ z = V₁.principal (hL p hp).2}

theorem Element.mem_interYs_of (z : V₁.Element) {L : List (Set α × Set β)} {X : Set α}
    (hall : ∀ p ∈ L, X ⊆ p.1 → z.mem p.2) : z.mem (interYs V₁.master L X) := by
  induction L with
  | nil => exact z.master_mem
  | cons p L ih =>
    have htail : ∀ q ∈ L, X ⊆ q.1 → z.mem q.2 :=
      fun q hq => hall q (List.mem_cons.mpr (Or.inr hq))
    by_cases hXp : X ⊆ p.1
    · have heq : interYs V₁.master (p :: L) X = p.2 ∩ interYs V₁.master L X := by
        rw [interYs_cons]; ext w
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 hXp, h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩
      rw [heq]
      exact z.inter_mem (hall p (List.mem_cons.mpr (Or.inl rfl)) hXp) (ih htail)
    · have heq : interYs V₁.master (p :: L) X = interYs V₁.master L X := by
        rw [interYs_cons]; ext w
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hXp, h⟩⟩
      rw [heq]
      exact ih htail

theorem leastMap_toElementMap_le_of_ub {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {x : V₀.Element} {z : V₁.Element}
    (hz : ∀ w ∈ leastMapVals L hL x, w ≤ z) :
    (leastMap L hL hcons).toElementMap x ≤ z := by
  rintro Y' ⟨X', hX'x, hX'mem, hY'mem, hsub⟩
  have hzint : z.mem (interYs V₁.master L X') := by
    apply Element.mem_interYs_of
    intro p hp hX'p
    have hp1x : x.mem p.1 := x.up_mem hX'x (hL p hp).1 hX'p
    have hle : V₁.principal (hL p hp).2 ≤ z := hz _ ⟨p, hp, hp1x, rfl⟩
    exact hle p.2 ⟨(hL p hp).2, subset_rfl⟩
  exact z.up_mem hzint hY'mem hsub

theorem val_le_leastMap_toElementMap {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {x : V₀.Element}
    {p : Set α × Set β} (hp : p ∈ L) (hp1x : x.mem p.1) :
    V₁.principal (hL p hp).2 ≤ (leastMap L hL hcons).toElementMap x := by
  have hmem : ((leastMap L hL hcons).toElementMap x).mem p.2 :=
    ⟨p.1, hp1x, leastMap_mem_stepFun hL hcons p hp⟩
  intro Z hZ
  exact ((leastMap L hL hcons).toElementMap x).up_mem hmem hZ.1 hZ.2

theorem leastMapVals_bounded {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) (x : V₀.Element) :
    V₁.Bounded (leastMapVals L hL x) := by
  refine ⟨(leastMap L hL hcons).toElementMap x, ?_⟩
  rintro w ⟨p, hp, hp1x, rfl⟩
  exact val_le_leastMap_toElementMap hL hcons hp hp1x

theorem toElementMap_leastMap_eq_sSup (L : List (Set α × Set β))
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) (x : V₀.Element) :
    (leastMap L hL hcons).toElementMap x
      = V₁.sSup (leastMapVals L hL x) (leastMapVals_bounded hL hcons x) := by
  apply le_antisymm
  · apply leastMap_toElementMap_le_of_ub hL hcons
    intro w hw
    exact V₁.le_sSup _ (leastMapVals_bounded hL hcons x) hw
  · apply V₁.sSup_le
    rintro w ⟨p, hp, hp1x, rfl⟩
    exact val_le_leastMap_toElementMap hL hcons hp hp1x
end

section
set_option linter.unusedVariables false

theorem example_328.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (L : List (Prod (Set α) (Set β)))
  (hL :
    ∀ (p : Prod (Set α) (Set β)),
      @Membership.mem (Prod (Set α) (Set β)) (List (Prod (Set α) (Set β))) (@List.instMembership (Prod (Set α) (Set β)))
          L p →
        And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ (@Prod.fst (Set α) (Set β) p))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ (@Prod.snd (Set α) (Set β) p)))
  (hcons :
    ∀ {X : Set α},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁
          (@DomainTheory.NeighbourhoodSystems.interYs α β
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) L X))
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
      (@DomainTheory.NeighbourhoodSystems.leastMap α β V₀ V₁ L hL fun {X : Set α} => @hcons X) x)
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup β V₁
      (@DomainTheory.NeighbourhoodSystems.leastMapVals α β V₀ V₁ L hL x)
      (@DomainTheory.NeighbourhoodSystems.leastMapVals_bounded α β V₀ V₁ L hL (fun {X : Set α} => @hcons X) x)) :=
  @DomainTheory.NeighbourhoodSystems.toElementMap_leastMap_eq_sSup
end
end

end DomainTheory.NeighbourhoodSystems
end
