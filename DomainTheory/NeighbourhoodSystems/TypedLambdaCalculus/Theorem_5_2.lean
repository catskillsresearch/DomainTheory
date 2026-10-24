module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
namespace Theorem52
/- concordance: source L2657 THEOREM 5.2 beta conversion -/
/-- **Theorem 5.2 (Scott 1981, PRG-19) — β as a map equation.** Substituting the constant `σ` for
the bound variable: `(λx.τ)(σ) = τ[σ/x]`, where the left side first abstracts (`curry g`) then
applies to the constant `σ`, and the right side substitutes `σ` directly. Both are approximable
maps `Γ → 𝒟'` and they are equal. -/
theorem beta (g : ApproximableMap (prod V₀ V₁) V₂) (σ : V₁.Element) :
    (evalMap V₁ V₂).comp (paired (curry g) (constMap V₀ σ))
      = g.comp (paired (idMap V₀) (constMap V₀ σ)) := by
  apply ext_of_toElementMap
  intro v
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply, toElementMap_curry_apply,
    toElementMap_constMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

end Theorem52
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2 (Scott 1981, PRG-19) — abstraction case (`inv` step).**
`(λx.λy.τ)(σ)(y) = τ[σ/x]` evaluated at `y`: the double-curry application law. The bound `y` is
carried inert past the substitution of `σ` for `x`, exactly Scott's
`(λx.λy.τ)(σ)(y) = (λx.τ)(σ)`. -/
theorem beta_abs (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) (v : V₀.Element) (σ : V₁.Element)
    (y : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry (curry g)).toElementMap v)).toElementMap σ)).toElementMap y
      = g.toElementMap (pair (pair v σ) y) := by
  rw [toElementMap_curry_apply, toElementMap_curry_apply]

end Theorem52
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2 (Scott 1981, PRG-19) — tuple case.**
`(λx.⟨τ₀, τ₁⟩)(σ) = ⟨(λx.τ₀)(σ), (λx.τ₁)(σ)⟩`: abstraction distributes over a tuple. -/
theorem beta_tuple (g₀ : ApproximableMap (prod V₀ V₁) V₂) (g₁ : ApproximableMap (prod V₀ V₁) V₃)
    (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry (paired g₀ g₁)).toElementMap v)).toElementMap x
      = pair ((toApproxMap ((curry g₀).toElementMap v)).toElementMap x)
          ((toApproxMap ((curry g₁).toElementMap v)).toElementMap x) := by
  rw [toElementMap_curry_apply, toElementMap_paired, toElementMap_curry_apply,
    toElementMap_curry_apply]

end Theorem52
end

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2, base value law (Scott 1981, PRG-19).** `(λx.τ)(σ) = τ[σ/x]` evaluated: applying
the abstraction `curry g` (in free-variable context `v`) to `x` substitutes, giving `g(v, x)`. -/
theorem subst_value (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x) :=
  toElementMap_curry_apply g v x

end Theorem52
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Theorem52
section
set_option linter.unusedVariables false

theorem theorem_52.{u_1, u_2, u_3, u_5} : And
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y))))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
      {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
      (g₀ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
      (g₁ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₃)
      (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum γ α_1)
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Sum γ α_1) V₁
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
          (@DomainTheory.NeighbourhoodSystems.toApproxMap β (Sum γ α_1) V₁
            (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              (@DomainTheory.NeighbourhoodSystems.curry α β (Sum γ α_1) V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.paired γ α_1 (Sum α β) V₂ V₃
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) g₀ g₁))
              v))
          x)
        (@DomainTheory.NeighbourhoodSystems.pair γ α_1 V₂ V₃
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g₀) v))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α_1 V₁ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β α_1 V₁ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β α_1 V₁ V₃) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β α_1 V₁ V₃)
                (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₃ g₁) v))
            x))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        V₂)
    (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x))) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y))))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
      {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
      (g₀ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
      (g₁ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₃)
      (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum γ α_1)
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Sum γ α_1) V₁
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
          (@DomainTheory.NeighbourhoodSystems.toApproxMap β (Sum γ α_1) V₁
            (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              (@DomainTheory.NeighbourhoodSystems.curry α β (Sum γ α_1) V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.paired γ α_1 (Sum α β) V₂ V₃
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) g₀ g₁))
              v))
          x)
        (@DomainTheory.NeighbourhoodSystems.pair γ α_1 V₂ V₃
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g₀) v))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α_1 V₁ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β α_1 V₁ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β α_1 V₁ V₃) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β α_1 V₁ V₃)
                (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₃ g₁) v))
            x))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        V₂)
    (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x)))
  (@And.intro
    (And
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y))))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
      {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
      (g₀ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
      (g₁ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₃)
      (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum γ α_1)
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Sum γ α_1) V₁
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
          (@DomainTheory.NeighbourhoodSystems.toApproxMap β (Sum γ α_1) V₁
            (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              (@DomainTheory.NeighbourhoodSystems.curry α β (Sum γ α_1) V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.paired γ α_1 (Sum α β) V₂ V₃
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) g₀ g₁))
              v))
          x)
        (@DomainTheory.NeighbourhoodSystems.pair γ α_1 V₂ V₃
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g₀) v))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α_1 V₁ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β α_1 V₁ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β α_1 V₁ V₃) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β α_1 V₁ V₃)
                (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₃ g₁) v))
            x)))
    (@And.intro
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y)))
      @DomainTheory.NeighbourhoodSystems.Theorem52.beta @DomainTheory.NeighbourhoodSystems.Theorem52.beta_abs)
    @DomainTheory.NeighbourhoodSystems.Theorem52.beta_tuple)
  @DomainTheory.NeighbourhoodSystems.Theorem52.subst_value
end

end DomainTheory.NeighbourhoodSystems.Theorem52
end
