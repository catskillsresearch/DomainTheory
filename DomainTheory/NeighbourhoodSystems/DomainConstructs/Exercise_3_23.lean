module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_15
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
section
variable {α β γ : Type*} (V : NeighborhoodSystem α)
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- There is at most one approximable mapping into the terminal domain `𝟙`: the codomain `|𝟙|`
is a subsingleton, so any two maps have the same elementwise action. -/
instance : Subsingleton (ApproximableMap V unitSys) :=
  ⟨fun _ _ => ext_of_toElementMap fun _ => Subsingleton.elim _ _⟩

/- concordance: source L1569 EXERCISE 3.23 cartesian closed category -/
/-- **Exercise 3.23 (Scott 1981, PRG-19).** `𝟙 = unitSys` is the *terminal object*: for every domain
`𝒟` there is a unique approximable mapping `𝒟 → 𝟙` (the constant map at `⊥`). -/
instance : Unique (ApproximableMap V unitSys) where
  default := constMap V (default : unitSys.Element)
  uniq _ := Subsingleton.elim _ _

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The cartesian-closed adjunction
`Hom(𝒟₀ × 𝒟₁, 𝒟₂) ≃o Hom(𝒟₀, (𝒟₁ → 𝒟₂))`, exhibiting `(𝒟₁ → 𝒟₂)` as the exponential object. This
is exactly `curryEquiv` of Theorem 3.12. -/
def homAdjunction (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) :=
  curryEquiv V₀ V₁ V₂

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The unique map to the terminal object, named. -/
def toUnit : ApproximableMap V unitSys := default

theorem toUnit_unique (f : ApproximableMap V unitSys) : f = toUnit V := Subsingleton.elim _ _
end

section
set_option linter.unusedVariables false

theorem example_323.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V DomainTheory.NeighbourhoodSystems.unitSys),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V DomainTheory.NeighbourhoodSystems.unitSys) f
    (@DomainTheory.NeighbourhoodSystems.toUnit α V) :=
  @DomainTheory.NeighbourhoodSystems.toUnit_unique
end
end

end DomainTheory.NeighbourhoodSystems
end
