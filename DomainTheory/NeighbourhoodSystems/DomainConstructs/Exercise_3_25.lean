module
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_20
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise325
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

/-- The **Sierpiński domain** `𝒪`: the system over a one-token type whose neighbourhoods are `Δ`
(`univ`) and `∅`. Its elements are `⊥` (only `Δ`) and `⊤` (also `∅`), i.e. the two-point domain. -/
def sierpinski : NeighborhoodSystem Unit where
  mem N := N = Set.univ ∨ N = ∅
  master := Set.univ
  master_nonempty := ⟨(), Set.mem_univ _⟩
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ _
    rcases hX with rfl | rfl
    · rcases hY with rfl | rfl
      · left; rw [Set.univ_inter]
      · right; rw [Set.univ_inter]
    · right; rw [Set.empty_inter]
  sub_master := fun _ => Set.subset_univ _

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- `mapOfOpen U : 𝒟 → 𝒪`. It always relates `X` to the blunt neighbourhood `univ` of `𝒪`, and
relates `X` to the sharp neighbourhood `∅` exactly when the basic open `[X]` lies inside `U`. As an
elementwise map it sends `x` to `⊤` iff `x ∈ U`. -/
def mapOfOpen (U : Set V.Element) : ApproximableMap V sierpinski where
  rel X Y := V.mem X ∧ (Y = Set.univ ∨ (Y = ∅ ∧ V.basicOpen X ⊆ U))
  rel_dom h := h.1
  rel_cod h := by
    rcases h.2 with rfl | ⟨rfl, _⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  master_rel := ⟨V.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    refine ⟨hX, ?_⟩
    rcases hY with rfl | ⟨rfl, hsub⟩
    · rcases hY' with rfl | ⟨rfl, hsub'⟩
      · left; rw [Set.univ_inter]
      · right; rw [Set.univ_inter]; exact ⟨rfl, hsub'⟩
    · rcases hY' with rfl | ⟨rfl, _⟩
      · right; rw [Set.inter_univ]; exact ⟨rfl, hsub⟩
      · right; rw [Set.inter_self]; exact ⟨rfl, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', ?_⟩
    rcases hY' with rfl | rfl
    · left; rfl
    · right
      refine ⟨rfl, ?_⟩
      rcases hY with rfl | ⟨rfl, hsub⟩
      · exact absurd (hYY' (Set.mem_univ ())) (by simp)
      · have hbo : V.basicOpen X' ⊆ V.basicOpen X := fun z hz => z.up_mem hz hX hX'X
        exact subset_trans hbo hsub

@[simp] theorem mapOfOpen_rel (U : Set V.Element) (X : Set α) (Y : Set Unit) :
    (mapOfOpen V U).rel X Y ↔ V.mem X ∧ (Y = Set.univ ∨ (Y = ∅ ∧ V.basicOpen X ⊆ U)) := Iff.rfl

/-- The decisive special case: `X (mapOfOpen U) ∅ ↔ [X] ⊆ U` (for a neighbourhood `X`). -/
theorem mapOfOpen_rel_empty (U : Set V.Element) (X : Set α) :
    (mapOfOpen V U).rel X ∅ ↔ V.mem X ∧ V.basicOpen X ⊆ U := by
  rw [mapOfOpen_rel]
  constructor
  · rintro ⟨hX, h⟩
    refine ⟨hX, ?_⟩
    rcases h with h | ⟨_, h⟩
    · exact absurd h Set.empty_ne_univ
    · exact h
  · rintro ⟨hX, h⟩
    exact ⟨hX, Or.inr ⟨rfl, h⟩⟩

/-- `openOfMap f = {x ∣ f(x) = ⊤} = ⋃ {[X] ∣ X f ∅}`: the points sent by `f` to the top of `𝒪`. -/
def openOfMap (f : ApproximableMap V sierpinski) : Set V.Element :=
  {x | ∃ X, x.mem X ∧ f.rel X ∅}

/-- `openOfMap f` is open: it is a union of basic opens `[X]`. -/
theorem openOfMap_isOpen (f : ApproximableMap V sierpinski) : IsOpen (openOfMap V f) := by
  constructor
  intro x hx
  obtain ⟨X, hxX, hf⟩ := hx
  exact ⟨X, hxX, fun z hz => ⟨X, hz, hf⟩⟩

end

section
set_option linter.unusedVariables false

theorem example_325.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (f :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V
      DomainTheory.NeighbourhoodSystems.Exercise325.sierpinski),
  @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V)
    (@DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap α V f) :=
  @DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap_isOpen
end

section
variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 3.25 (core).** The open subsets of `|𝒟|` (ordered by `⊆`) are order-isomorphic to the
approximable maps `𝒟 → 𝒪`. -/
def openIso (V : NeighborhoodSystem α) :
    {U : Set V.Element // IsOpen U} ≃o ApproximableMap V sierpinski where
  toFun U := mapOfOpen V U.1
  invFun f := ⟨openOfMap V f, openOfMap_isOpen V f⟩
  left_inv U := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨X, hxX, hrel⟩
      rw [mapOfOpen_rel_empty] at hrel
      exact hrel.2 hxX
    · intro hx
      obtain ⟨X, hxX, hsub⟩ := U.2.out x hx
      exact ⟨X, hxX, (mapOfOpen_rel_empty V U.1 X).mpr ⟨x.sub hxX, hsub⟩⟩
  right_inv f := by
    apply ApproximableMap.ext
    intro X Y
    rw [mapOfOpen_rel]
    constructor
    · rintro ⟨hX, hd⟩
      rcases hd with rfl | ⟨rfl, hsub⟩
      · exact f.mono f.master_rel (V.sub_master hX) (Set.subset_univ _) hX (Or.inl rfl)
      · have hpr : V.principal hX ∈ V.basicOpen X := ⟨hX, subset_rfl⟩
        obtain ⟨X', hX', hf⟩ := hsub hpr
        exact f.mono hf hX'.2 subset_rfl hX (Or.inr rfl)
    · intro hf
      refine ⟨f.rel_dom hf, ?_⟩
      rcases f.rel_cod hf with rfl | rfl
      · left; rfl
      · exact Or.inr ⟨rfl, fun z hz => ⟨X, hz, hf⟩⟩
  map_rel_iff' := by
    intro a b
    show mapOfOpen V a.1 ≤ mapOfOpen V b.1 ↔ a ≤ b
    rw [ApproximableMap.le_iff]
    constructor
    · intro h x hx
      obtain ⟨X, hxX, hsub⟩ := a.2.out x hx
      have hrelB := h X ∅ ((mapOfOpen_rel_empty V a.1 X).mpr ⟨x.sub hxX, hsub⟩)
      rw [mapOfOpen_rel_empty] at hrelB
      exact hrelB.2 hxX
    · intro h X Y hrel
      rw [mapOfOpen_rel] at hrel ⊢
      obtain ⟨hX, hd⟩ := hrel
      refine ⟨hX, ?_⟩
      rcases hd with hu | ⟨he, hsub⟩
      · exact Or.inl hu
      · exact Or.inr ⟨he, fun z hz => h (hsub hz)⟩

/- concordance: source L1583 EXERCISE 3.25 opens form a domain -/
/-- **Exercise 3.25.** The family of open subsets of `|𝒟|`, ordered by inclusion, is
order-isomorphic to the domain `|𝒟 → 𝒪|` of the Sierpiński function space — hence *is* (isomorphic
to) a domain. This uses Theorem 3.10 (`funSpaceEquiv`) exactly as Scott directs. -/
def opensReprIso (V : NeighborhoodSystem α) :
    {U : Set V.Element // IsOpen U} ≃o (funSpace V sierpinski).Element :=
  (openIso V).trans (funSpaceEquiv V sierpinski).symm
end
end

end DomainTheory.NeighbourhoodSystems.Exercise325
end
