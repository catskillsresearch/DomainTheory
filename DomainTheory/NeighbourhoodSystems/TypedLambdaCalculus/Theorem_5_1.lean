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
namespace Theorem51

/- concordance: source L2599 THEOREM 5.1 terms denote approximable maps -/
/-- **Theorem 5.1, abstraction case (Scott 1981, PRG-19).** If `⟦σ⟧ : Γ × 𝒟ₙ → 𝒟'` is approximable,
then `λx.σ` is interpreted by `curry ⟦σ⟧ : Γ → (𝒟ₙ → 𝒟')` (approximable by Thm 3.12), with value
`(λx.σ)(v)(x) = σ(v, x)`. -/
theorem abs_apply (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x) :=
  toElementMap_curry_apply g v x

/-- **Theorem 5.1, application case (Scott 1981, PRG-19).** If `⟦σ₀⟧ : Γ → (𝒟₀ → 𝒟₁)` and
`⟦σ₁⟧ : Γ → 𝒟₀` are approximable, then `σ₀(σ₁)` is interpreted by `eval ∘ ⟨⟦σ₀⟧, ⟦σ₁⟧⟩`
(approximable by Thm 3.11 and Thm 2.5), with value `(σ₀ w)(σ₁ w)`. -/
theorem app_apply (F : ApproximableMap V₂ (funSpace V₀ V₁)) (G : ApproximableMap V₂ V₀)
    (w : V₂.Element) :
    ((evalMap V₀ V₁).comp (paired F G)).toElementMap w
      = (toApproxMap (F.toElementMap w)).toElementMap (G.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply]

/-- **Theorem 5.1, constant case (Scott 1981, PRG-19).** A constant `k` is interpreted by the
constant map, which is approximable with value `k`. -/
theorem const_apply (k : V₁.Element) (x : V₀.Element) :
    (constMap V₀ k).toElementMap x = k := toElementMap_constMap k x

/-- **Theorem 5.1, tuple case (Scott 1981, PRG-19).** If `⟦σ₀⟧, ⟦σ₁⟧` are approximable, so is the
tuple `⟨⟦σ₀⟧, ⟦σ₁⟧⟩ = paired`, with value `⟨σ₀(w), σ₁(w)⟩`. -/
theorem tuple_apply (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) (w : V₂.Element) :
    (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w) :=
  toElementMap_paired f g w

/-- **Theorem 5.1, variable case (Scott 1981, PRG-19).** A free variable is interpreted by a
projection of the context; the projections are approximable with `p₀⟨x,y⟩ = x`, `p₁⟨x,y⟩ = y`. -/
theorem var_fst (x : V₀.Element) (y : V₁.Element) :
    (proj₀ V₀ V₁).toElementMap (pair x y) = x := by rw [toElementMap_proj₀, fst_pair]

end Theorem51
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Theorem51
section
set_option linter.unusedVariables false

theorem theorem_51.{u_1, u_2, u_3} : And
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
      (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁)
      (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ (Sum α β) V₂
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ f g) w)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ f w)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁ g w))))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) α
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₀ (@DomainTheory.NeighbourhoodSystems.proj₀ α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      x) :=
  @And.intro
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
      (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁)
      (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ (Sum α β) V₂
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ f g) w)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ f w)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁ g w))))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) α
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₀ (@DomainTheory.NeighbourhoodSystems.proj₀ α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      x)
  (@And.intro
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
      (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁)
      (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ (Sum α β) V₂
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ f g) w)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ f w)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁ g w)))
    (@And.intro
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k)
      (@And.intro
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w)))
        @DomainTheory.NeighbourhoodSystems.Theorem51.abs_apply @DomainTheory.NeighbourhoodSystems.Theorem51.app_apply)
      @DomainTheory.NeighbourhoodSystems.Theorem51.const_apply)
    @DomainTheory.NeighbourhoodSystems.Theorem51.tuple_apply)
  @DomainTheory.NeighbourhoodSystems.Theorem51.var_fst
end

end DomainTheory.NeighbourhoodSystems.Theorem51
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51

theorem var_snd (x : V₀.Element) (y : V₁.Element) :
    (proj₁ V₀ V₁).toElementMap (pair x y) = y := by rw [toElementMap_proj₁, snd_pair]

end Theorem51

namespace Theorem52

end Theorem52

end
end DomainTheory.NeighbourhoodSystems
end
