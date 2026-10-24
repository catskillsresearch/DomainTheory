module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_4
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_7
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_21
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_16
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem_5_6
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_7
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_22
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
section ProjectionPair
variable (i : ApproximableMap D E) (j : ApproximableMap E D)
/- concordance: source L3957 LEMMA 6.15 subdomains from projection pairs -/
/-- **Lemma 6.15 (Scott 1981, PRG-19).** A projection pair `i : D → E`, `j : E → D` with
`j ∘ i = I_D` and `i ∘ j ⊆ I_E` exhibits `D` as a subdomain of `E`: `D ⊴ E`. This is the converse
of Proposition 6.12 (`Subsystem.projectionPair`). -/
theorem trianglelefteq_of_projectionPair (hji : j.comp i = idMap D)
    (hij : i.comp j ≤ idMap E) : D ⊴ E :=
  ⟨Dprime i j, Dprime_subsystem i j, ⟨dprimeEquiv i j hji hij⟩⟩

end ProjectionPair
end

section
set_option linter.unusedVariables false

theorem theorem_615.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  (i : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β D E)
  (j : @DomainTheory.NeighbourhoodSystems.ApproximableMap β α E D),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D E D j i)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D) →
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
            (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap β β E E)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β α β E D E i j)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β E) →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E :=
  @DomainTheory.NeighbourhoodSystems.trianglelefteq_of_projectionPair
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems
namespace Subsystem
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*}
variable {D E : NeighborhoodSystem α}

/-- **A projection pair (Definition 6.13 vocabulary).** Bundles Scott's `i, j` together with the two
laws, ready for reuse in monotone/continuous-on-domains functors and the existence Theorem 6.14. -/
structure ProjectionPair (D E : NeighborhoodSystem α) where
  /-- The injection `i : D → E`. -/
  inj : ApproximableMap D E
  /-- The projection `j : E → D`. -/
  proj : ApproximableMap E D
  /-- `j ∘ i = I_D`. -/
  proj_comp_inj : proj.comp inj = idMap D
  /-- `i ∘ j ⊆ I_E`. -/
  inj_comp_proj_le : inj.comp proj ≤ idMap E
end

end Subsystem
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **The injection `i : D → E` of Proposition 6.12.** As a neighbourhood relation,
`X i Y ↔ X ∈ D ∧ Y ∈ E ∧ X ⊆ Y`. Element-wise (see `toElementMap_inj`) it is Scott's
`i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}`. -/
def inj (h : D ◁ E) : ApproximableMap D E where
  rel X Y := D.mem X ∧ E.mem Y ∧ X ⊆ Y
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨D.master_mem, E.master_mem, h.master_eq.subset⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    exact ⟨hX, E.inter_mem hY hY' (h.sub hX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (hX'X.trans hXY).trans hYY'⟩

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

@[simp] theorem inj_rel (h : D ◁ E) {X Y : Set α} :
    (h.inj).rel X Y ↔ D.mem X ∧ E.mem Y ∧ X ⊆ Y := Iff.rfl

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **The projection `j : E → D` of Proposition 6.12.** As a neighbourhood relation,
`Y j X ↔ Y ∈ E ∧ X ∈ D ∧ Y ⊆ X`. Element-wise (see `toElementMap_proj`) it is Scott's
`j(y) = y ∩ D`. The `inter_right` law is exactly where Definition 6.10's consistency clause
(`inter_closed`) is used. -/
def proj (h : D ◁ E) : ApproximableMap E D where
  rel Y X := E.mem Y ∧ D.mem X ∧ Y ⊆ X
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨E.master_mem, D.master_mem, h.master_eq.symm.subset⟩
  inter_right := by
    rintro Y X X' ⟨hY, hX, hYX⟩ ⟨_, hX', hYX'⟩
    have hEinter : E.mem (X ∩ X') :=
      E.inter_mem (h.sub hX) (h.sub hX') hY (Set.subset_inter hYX hYX')
    exact ⟨hY, h.inter_closed hX hX' hEinter, Set.subset_inter hYX hYX'⟩
  mono := by
    rintro Y Y' X X' ⟨_, _, hYX⟩ hY'Y hXX' hY' hX'
    exact ⟨hY', hX', (hY'Y.trans hYX).trans hXX'⟩

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

@[simp] theorem proj_rel (h : D ◁ E) {Y X : Set α} :
    (h.proj).rel Y X ↔ E.mem Y ∧ D.mem X ∧ Y ⊆ X := Iff.rfl

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Proposition 6.12, second law: `i ∘ j ⊆ I_E`.** A round trip `Y ⊆ X ⊆ Y'` through a common
`D`-neighbourhood `X` is in particular `Y ⊆ Y'` on `E`. The reverse inclusion fails (not every
consistent `E`-pair factors through `D`), so this is an inclusion of relations, not an equality. -/
theorem inj_comp_proj_le (h : D ◁ E) : h.inj.comp h.proj ≤ idMap E := by
  intro Y Y' hr
  obtain ⟨X, ⟨hEY, _, hYX⟩, _, hEY', hXY'⟩ := hr
  exact ⟨hEY, hEY', hYX.trans hXY'⟩

end Subsystem
end

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Proposition 6.12, first law: `j ∘ i = I_D`.** Each side relates `X` and `Z` exactly when
`X, Z ∈ D` and `X ⊆ Z`: a round trip `X ⊆ Y ⊆ Z` through an `E`-neighbourhood `Y` collapses to
`X ⊆ Z` (forward), and `X ⊆ Z` factors through `Y = Z` (backward). Proved relationally, so
**choice-free**. -/
theorem proj_comp_inj (h : D ◁ E) : h.proj.comp h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, _, hZ, hYZ⟩
    exact ⟨hX, hZ, hXY.trans hYZ⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨Z, ⟨hX, h.sub hZ, hXZ⟩, h.sub hZ, hZ, subset_rfl⟩

end Subsystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Subsystem
section
set_option linter.unusedVariables false

theorem theorem_612.{u_1} : And
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E D E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α D E D
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D)) :=
  @And.intro
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E D E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α D E D
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D))
  @DomainTheory.NeighbourhoodSystems.Subsystem.inj_comp_proj_le
  @DomainTheory.NeighbourhoodSystems.Subsystem.proj_comp_inj
end

end DomainTheory.NeighbourhoodSystems.Subsystem
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Subsystem

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- The set `{x ∈ |𝒟| ∣ g(x) ⊑ y}` of the first formula. By the Galois connection it is the
down-set `{x ∣ x ⊑ h(y)}` of `h(y)`. -/
def lowerSet (P : ProjectionPair D E) (y : E.Element) : Set D.Element :=
  {x | P.inj.toElementMap x ≤ y}

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

@[simp] theorem mem_lowerSet (P : ProjectionPair D E) {y : E.Element} {x : D.Element} :
    x ∈ P.lowerSet y ↔ P.inj.toElementMap x ≤ y := Iff.rfl

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- The set `{y ∈ |ℰ| ∣ x ⊑ h(y)}` of the second formula. By the Galois connection it is the
up-set `{y ∣ g(x) ⊑ y}` of `g(x)`. -/
def upperSet (P : ProjectionPair D E) (x : D.Element) : Set E.Element :=
  {y | x ≤ P.proj.toElementMap y}

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


@[simp] theorem mem_upperSet (P : ProjectionPair D E) {x : D.Element} {y : E.Element} :
    y ∈ P.upperSet x ↔ x ≤ P.proj.toElementMap y := Iff.rfl

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


end Subsystem.ProjectionPair
end
end DomainTheory.NeighbourhoodSystems
end
