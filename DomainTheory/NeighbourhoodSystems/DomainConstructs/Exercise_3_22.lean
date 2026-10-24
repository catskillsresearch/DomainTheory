module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_21

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
/- concordance: source L1545 EXERCISE 3.22 composition combinator -/
/-- **Exercise 3.22 (Scott 1981, PRG-19).** The composition mapping
`comp : (𝒟₁ → 𝒟₂) × (𝒟₀ → 𝒟₁) → (𝒟₀ → 𝒟₂)`, `comp = curry(compApp)`. -/
def compMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compApp V₀ V₁ V₂)

/-- `compApp(⟨⟨g, f⟩, x⟩) = g(f(x))`. -/
theorem toElementMap_compApp (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (compApp V₀ V₁ V₂).toElementMap (pair (pair Gφ Fφ) x)
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compApp]
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

/-- **Exercise 3.22 (Scott 1981, PRG-19).** `comp(g, f) = g ∘ f`: applying the value
`comp(⟨g, f⟩) ∈ |𝒟₀ → 𝒟₂|` to `x` gives `g(f(x))`. -/
theorem toElementMap_compMap_apply (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))).toElementMap x
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compMap, toElementMap_curry_apply, toElementMap_compApp]

/-- **Exercise 3.22 (Scott 1981, PRG-19).** The relational form `comp(g, f) = g ∘ f`: the value of
`comp` at `⟨g, f⟩`, read back as an approximable map, is the composition of the approximable maps. -/
theorem toApproxMap_compMap (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))
      = (toApproxMap Gφ).comp (toApproxMap Fφ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_compMap_apply, toElementMap_comp]
end

section
set_option linter.unusedVariables false

theorem example_322.{u_1, u_2, u_3} : And
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
          (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V₀ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ)))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ) x))) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
          (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V₀ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ)))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ) x)))
  @DomainTheory.NeighbourhoodSystems.toApproxMap_compMap @DomainTheory.NeighbourhoodSystems.toElementMap_compMap_apply
end

section
variable {α β γ : Type*} (V : NeighborhoodSystem α)
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- There is at most one approximable mapping into the terminal domain `𝟙`: the codomain `|𝟙|`
is a subsingleton, so any two maps have the same elementwise action. -/
instance : Subsingleton (ApproximableMap V unitSys) :=
  ⟨fun _ _ => ext_of_toElementMap fun _ => Subsingleton.elim _ _⟩

end
end
end DomainTheory.NeighbourhoodSystems
end
