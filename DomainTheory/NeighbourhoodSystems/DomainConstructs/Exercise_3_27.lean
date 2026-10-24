module
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_22
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6
public import Mathlib.Order.Directed
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise327
section
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The **graph** of an approximable map, as a set of neighbourhood pairs. -/
def graph (f : ApproximableMap V₀ V₁) : Set (Set α × Set β) := {p | f.rel p.1 p.2}

@[simp] theorem mem_graph {f : ApproximableMap V₀ V₁} {p : Set α × Set β} :
    p ∈ graph f ↔ f.rel p.1 p.2 := Iff.rfl

/-- Scott's family `C`: all graphs of approximable maps `𝒟₀ → 𝒟₁`. -/
def C (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Set (Set (Set α × Set β)) :=
  Set.range (graph (V₀ := V₀) (V₁ := V₁))

theorem C_nonempty : (C V₀ V₁).Nonempty :=
  ⟨graph (constMap V₀ V₁.bot), constMap V₀ V₁.bot, rfl⟩

theorem graph_injective : Function.Injective (graph (V₀ := V₀) (V₁ := V₁)) :=
  fun _ _ h => ApproximableMap.ext fun X Y => Set.ext_iff.mp h (X, Y)

/-- `graph` is an order-isomorphism of approximable maps (under `⊑`) onto the family `C`
(under `⊆`). -/
noncomputable def graphEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ V₁ ≃o {X : Set (Set α × Set β) // X ∈ C V₀ V₁} where
  toFun f := ⟨graph f, f, rfl⟩
  invFun X := X.2.choose
  left_inv f := graph_injective (⟨graph f, f, rfl⟩ : {X // X ∈ C V₀ V₁}).2.choose_spec
  right_inv X := Subtype.ext X.2.choose_spec
  map_rel_iff' := by
    intro f g
    show graph f ⊆ graph g ↔ f ≤ g
    rw [ApproximableMap.le_iff]
    exact ⟨fun h X Y hf => h (a := (X, Y)) hf, fun h p hp => h p.1 p.2 hp⟩

/-- The **join** `⋁ 𝒮` of a directed family of approximable maps: `X (⋁𝒮) Y` iff `(X, Y)` lies in
some member. Directedness is what restores the intersectivity condition (ii). -/
def joinMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁) (hne : 𝒮.Nonempty)
    (hdir : DirectedOn (· ⊆ ·) 𝒮) : ApproximableMap V₀ V₁ where
  rel X Y := ∃ S ∈ 𝒮, (X, Y) ∈ S
  rel_dom := by rintro X Y ⟨S, hS, hp⟩; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.rel_dom hp
  rel_cod := by rintro X Y ⟨S, hS, hp⟩; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.rel_cod hp
  master_rel := by
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact ⟨graph f, hS, f.master_rel⟩
  inter_right := by
    rintro X Y Y' ⟨S, hS, hp⟩ ⟨S', hS', hp'⟩
    obtain ⟨S₃, hS₃, hSS₃, hS'S₃⟩ := hdir S hS S' hS'
    obtain ⟨f, rfl⟩ := h𝒮 hS₃
    exact ⟨graph f, hS₃, f.inter_right (hSS₃ hp) (hS'S₃ hp')⟩
  mono := by
    rintro X X' Y Y' ⟨S, hS, hp⟩ hX'X hYY' hX' hY'
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact ⟨graph f, hS, f.mono hp hX'X hYY' hX' hY'⟩

/-- The pointwise **meet** `⋀ 𝒮` of a family of approximable maps (drawn from `C`): `X (⋀𝒮) Y` iff
`(X, Y)` lies in every member of `𝒮`. -/
def meetMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁) (hne : 𝒮.Nonempty) :
    ApproximableMap V₀ V₁ where
  rel X Y := ∀ S ∈ 𝒮, (X, Y) ∈ S
  rel_dom := by
    intro X Y h
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.rel_dom (h _ hS)
  rel_cod := by
    intro X Y h
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.rel_cod (h _ hS)
  master_rel := by
    intro S hS; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.master_rel
  inter_right := by
    intro X Y Y' hY hY' S hS
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.inter_right (hY _ hS) (hY' _ hS)
  mono := by
    intro X X' Y Y' h hX'X hYY' hX' hY' S hS
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.mono (h _ hS) hX'X hYY' hX' hY'

theorem sInter_eq_graph_meetMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁)
    (hne : 𝒮.Nonempty) : ⋂₀ 𝒮 = graph (meetMap 𝒮 h𝒮 hne) := by
  ext p
  simp only [Set.mem_sInter, mem_graph]
  exact ⟨fun h S hS => h S hS, fun h S hS => h S hS⟩

/-- **Exercise 2.22 hypothesis (i).** `C` is closed under non-empty intersections. -/
theorem C_inter : ∀ 𝒮 : Set (Set (Set α × Set β)), 𝒮.Nonempty → 𝒮 ⊆ C V₀ V₁ → ⋂₀ 𝒮 ∈ C V₀ V₁ := by
  intro 𝒮 hne h𝒮
  rw [sInter_eq_graph_meetMap 𝒮 h𝒮 hne]
  exact ⟨meetMap 𝒮 h𝒮 hne, rfl⟩

theorem sUnion_eq_graph_joinMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁)
    (hne : 𝒮.Nonempty) (hdir : DirectedOn (· ⊆ ·) 𝒮) :
    ⋃₀ 𝒮 = graph (joinMap 𝒮 h𝒮 hne hdir) := by
  ext p
  simp only [Set.mem_sUnion, mem_graph]
  exact ⟨fun ⟨S, hS, hp⟩ => ⟨S, hS, hp⟩, fun ⟨S, hS, hp⟩ => ⟨S, hS, hp⟩⟩

/-- **Exercise 2.22 hypothesis (ii).** `C` is closed under directed unions. -/
theorem C_dir : ∀ 𝒮 : Set (Set (Set α × Set β)), 𝒮.Nonempty → 𝒮 ⊆ C V₀ V₁ →
    DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C V₀ V₁ := by
  intro 𝒮 hne h𝒮 hdir
  rw [sUnion_eq_graph_joinMap 𝒮 h𝒮 hne hdir]
  exact ⟨joinMap 𝒮 h𝒮 hne hdir, rfl⟩

end

section
set_option linter.unusedVariables false

theorem example_327.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (𝒮 : Set (Set (Prod (Set α) (Set β)))),
  @Set.Nonempty (Set (Prod (Set α) (Set β))) 𝒮 →
    @LE.le (Set (Set (Prod (Set α) (Set β)))) (@Set.instLE (Set (Prod (Set α) (Set β)))) 𝒮
        (@DomainTheory.NeighbourhoodSystems.Exercise327.C α β V₀ V₁) →
      @DirectedOn (Set (Prod (Set α) (Set β)))
          (fun (x1 x2 : Set (Prod (Set α) (Set β))) =>
            @LE.le (Set (Prod (Set α) (Set β))) (@Set.instLE (Prod (Set α) (Set β))) x1 x2)
          𝒮 →
        @Membership.mem (Set (Prod (Set α) (Set β))) (Set (Set (Prod (Set α) (Set β))))
          (@Set.instMembership (Set (Prod (Set α) (Set β))))
          (@DomainTheory.NeighbourhoodSystems.Exercise327.C α β V₀ V₁) (@Set.sUnion (Prod (Set α) (Set β)) 𝒮) :=
  @DomainTheory.NeighbourhoodSystems.Exercise327.C_dir
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
/- concordance: source L1627 EXERCISE 3.27 function space via closure -/
/-- **Exercise 3.27.** The function space `|𝒟₀ → 𝒟₁|` is (order-)isomorphic to the domain produced by
the *abstract* representation theorem (Exercise 2.22) applied to the family `C` of graphs of
approximable maps. This re-proves that approximable mappings form a domain without appealing to the
explicit step-set neighbourhood system of Definition 3.8 — composing Exercise 2.22's `reprIso` with
the graph isomorphism (`graphEquiv`) and Theorem 3.10 (`funSpaceEquiv`). -/
noncomputable def funSpaceReprIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (Exercise222.reprSystem (C V₀ V₁) C_inter C_nonempty).Element ≃o (funSpace V₀ V₁).Element :=
  (Exercise222.reprIso (C V₀ V₁) C_inter C_nonempty C_dir).trans
    ((graphEquiv V₀ V₁).symm.trans (funSpaceEquiv V₀ V₁).symm)
end
end

end DomainTheory.NeighbourhoodSystems.Exercise327
end
