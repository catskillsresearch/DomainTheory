module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.paired_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodMap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prod_isEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.proju2080_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.proju2081_isComputable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_74.{u_1, u_2, u_4, u_5, u_3} : And
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
                (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  {h₀ :
                    ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                  {h₁ :
                    ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) α
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₀
                    (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)))
              (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                {h₀ :
                  ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                {h₁ :
                  ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) β
                  (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                  (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₁
                  (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)))
            (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
              {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
              {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
              {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
              {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
              {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
              {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
              {h₀' :
                ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
              {h₁' :
                ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
              (Q₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀')
              (Q₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁')
              {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
              {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
              @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ Q₀ f →
                @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ Q₁ g →
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) (Option (Sum α' β'))
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
                    (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α' β' V₀' V₁' h₀' h₁' Q₀ Q₁)
                    (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)))
          (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
            {P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂}
            {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
            {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
            {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀}
            {b : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁},
            @DomainTheory.NeighbourhoodSystems.ComputableMap γ α V₂ V₀ P₂ P₀ a →
              @DomainTheory.NeighbourhoodSystems.ComputableMap γ β V₂ V₁ P₂ P₁ b →
                @DomainTheory.NeighbourhoodSystems.ComputableMap γ (Sum α β) V₂
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) P₂
                  (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                  (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ a b)))
        (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
          {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
          {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
          {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
          {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
          {P₀' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀'}
          {P₁' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁'}
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
          {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ P₀' f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ P₁' g →
              @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) (Sum α' β')
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α' β' V₀' V₁' P₀' P₁')
                (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Sum α β)
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
      @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) α (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        V₀ (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₀
        (@DomainTheory.NeighbourhoodSystems.proj₀ α β V₀ V₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) β (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₁ (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₁
      (@DomainTheory.NeighbourhoodSystems.proj₁ α β V₀ V₁)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
                (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  {h₀ :
                    ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                  {h₁ :
                    ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) α
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₀
                    (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)))
              (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                {h₀ :
                  ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                {h₁ :
                  ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) β
                  (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                  (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₁
                  (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)))
            (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
              {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
              {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
              {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
              {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
              {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
              {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
              {h₀' :
                ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
              {h₁' :
                ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
              (Q₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀')
              (Q₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁')
              {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
              {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
              @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ Q₀ f →
                @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ Q₁ g →
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) (Option (Sum α' β'))
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
                    (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α' β' V₀' V₁' h₀' h₁' Q₀ Q₁)
                    (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)))
          (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
            {P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂}
            {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
            {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
            {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀}
            {b : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁},
            @DomainTheory.NeighbourhoodSystems.ComputableMap γ α V₂ V₀ P₂ P₀ a →
              @DomainTheory.NeighbourhoodSystems.ComputableMap γ β V₂ V₁ P₂ P₁ b →
                @DomainTheory.NeighbourhoodSystems.ComputableMap γ (Sum α β) V₂
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) P₂
                  (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                  (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ a b)))
        (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
          {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
          {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
          {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
          {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
          {P₀' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀'}
          {P₁' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁'}
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
          {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ P₀' f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ P₁' g →
              @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) (Sum α' β')
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α' β' V₀' V₁' P₀' P₁')
                (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Sum α β)
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
      @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) α (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        V₀ (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₀
        (@DomainTheory.NeighbourhoodSystems.proj₀ α β V₀ V₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) β (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₁ (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₁
      (@DomainTheory.NeighbourhoodSystems.proj₁ α β V₀ V₁))
  (@And.intro
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
                (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  {h₀ :
                    ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                  {h₁ :
                    ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) α
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₀
                    (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)))
              (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                {h₀ :
                  ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                {h₁ :
                  ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) β
                  (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                  (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₁
                  (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)))
            (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
              {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
              {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
              {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
              {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
              {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
              {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
              {h₀' :
                ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
              {h₁' :
                ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
              (Q₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀')
              (Q₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁')
              {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
              {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
              @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ Q₀ f →
                @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ Q₁ g →
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) (Option (Sum α' β'))
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
                    (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α' β' V₀' V₁' h₀' h₁' Q₀ Q₁)
                    (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)))
          (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
            {P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂}
            {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
            {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
            {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀}
            {b : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁},
            @DomainTheory.NeighbourhoodSystems.ComputableMap γ α V₂ V₀ P₂ P₀ a →
              @DomainTheory.NeighbourhoodSystems.ComputableMap γ β V₂ V₁ P₂ P₁ b →
                @DomainTheory.NeighbourhoodSystems.ComputableMap γ (Sum α β) V₂
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) P₂
                  (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                  (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ a b)))
        (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
          {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
          {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
          {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
          {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
          {P₀' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀'}
          {P₁' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁'}
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
          {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ P₀' f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ P₁' g →
              @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) (Sum α' β')
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α' β' V₀' V₁' P₀' P₁')
                (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Sum α β)
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
      @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) α (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        V₀ (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₀
        (@DomainTheory.NeighbourhoodSystems.proj₀ α β V₀ V₁))
    (@And.intro
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
                (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  {h₀ :
                    ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                  {h₁ :
                    ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) α
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₀
                    (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)))
              (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                {h₀ :
                  ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                {h₁ :
                  ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) β
                  (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                  (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₁
                  (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)))
            (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
              {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
              {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
              {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
              {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
              {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
              {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
              {h₀' :
                ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
              {h₁' :
                ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
              (Q₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀')
              (Q₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁')
              {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
              {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
              @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ Q₀ f →
                @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ Q₁ g →
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) (Option (Sum α' β'))
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
                    (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α' β' V₀' V₁' h₀' h₁' Q₀ Q₁)
                    (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)))
          (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
            {P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂}
            {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
            {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
            {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀}
            {b : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁},
            @DomainTheory.NeighbourhoodSystems.ComputableMap γ α V₂ V₀ P₂ P₀ a →
              @DomainTheory.NeighbourhoodSystems.ComputableMap γ β V₂ V₁ P₂ P₁ b →
                @DomainTheory.NeighbourhoodSystems.ComputableMap γ (Sum α β) V₂
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) P₂
                  (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                  (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ a b)))
        (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
          {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
          {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
          {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
          {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
          {P₀' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀'}
          {P₁' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁'}
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
          {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ P₀' f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ P₁' g →
              @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) (Sum α' β')
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α' β' V₀' V₁' P₀' P₁')
                (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Sum α β)
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
      (@And.intro
        (And
          (And
            (And
              (And
                (And
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
                (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  {h₀ :
                    ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                  {h₁ :
                    ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) α
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₀
                    (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)))
              (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                {h₀ :
                  ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                {h₁ :
                  ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) β
                  (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                  (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₁
                  (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)))
            (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
              {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
              {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
              {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
              {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
              {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
              {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
              {h₀' :
                ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
              {h₁' :
                ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
              (Q₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀')
              (Q₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁')
              {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
              {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
              @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ Q₀ f →
                @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ Q₁ g →
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) (Option (Sum α' β'))
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
                    (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α' β' V₀' V₁' h₀' h₁' Q₀ Q₁)
                    (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)))
          (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
            {P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂}
            {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
            {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
            {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀}
            {b : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁},
            @DomainTheory.NeighbourhoodSystems.ComputableMap γ α V₂ V₀ P₂ P₀ a →
              @DomainTheory.NeighbourhoodSystems.ComputableMap γ β V₂ V₁ P₂ P₁ b →
                @DomainTheory.NeighbourhoodSystems.ComputableMap γ (Sum α β) V₂
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) P₂
                  (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                  (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ a b)))
        (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
          {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
          {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
          {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
          {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
          {P₀' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀'}
          {P₁' : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁'}
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
          {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ P₀' f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ P₁' g →
              @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) (Sum α' β')
                (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                (@DomainTheory.NeighbourhoodSystems.prodPresentation α' β' V₀' V₁' P₀' P₁')
                (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f g))
        (@And.intro
          (And
            (And
              (And
                (And
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
                (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  {h₀ :
                    ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                  {h₁ :
                    ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) α
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₀
                    (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)))
              (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                {h₀ :
                  ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                {h₁ :
                  ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) β
                  (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                  (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₁
                  (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)))
            (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
              {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
              {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
              {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
              {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
              {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
              {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
              {h₀' :
                ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
              {h₁' :
                ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
              (Q₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀')
              (Q₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁')
              {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
              {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
              @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ Q₀ f →
                @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ Q₁ g →
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) (Option (Sum α' β'))
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
                    (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α' β' V₀' V₁' h₀' h₁' Q₀ Q₁)
                    (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g)))
          (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
            {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
            {P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂}
            {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
            {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
            {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀}
            {b : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁},
            @DomainTheory.NeighbourhoodSystems.ComputableMap γ α V₂ V₀ P₂ P₀ a →
              @DomainTheory.NeighbourhoodSystems.ComputableMap γ β V₂ V₁ P₂ P₁ b →
                @DomainTheory.NeighbourhoodSystems.ComputableMap γ (Sum α β) V₂
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) P₂
                  (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁)
                  (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ a b))
          (@And.intro
            (And
              (And
                (And
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
                (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  {h₀ :
                    ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                  {h₁ :
                    ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) α
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₀
                    (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)))
              (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                {h₀ :
                  ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                {h₁ :
                  ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) β
                  (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                  (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₁
                  (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁)))
            (∀ {α : Type u_1} {β : Type u_2} {α' : Type u_4} {β' : Type u_5}
              {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
              {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
              {P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀}
              {P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁}
              {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
              {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
              {h₀' :
                ∀ (X : Set α'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α' V₀' X → @Set.Nonempty α' X}
              {h₁' :
                ∀ (Y : Set β'), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β' V₁' Y → @Set.Nonempty β' Y}
              (Q₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α' V₀')
              (Q₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β' V₁')
              {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
              {g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
              @DomainTheory.NeighbourhoodSystems.ComputableMap α α' V₀ V₀' P₀ Q₀ f →
                @DomainTheory.NeighbourhoodSystems.ComputableMap β β' V₁ V₁' P₁ Q₁ g →
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) (Option (Sum α' β'))
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
                    (@DomainTheory.NeighbourhoodSystems.sum α' β' V₀' V₁' h₀' h₁')
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α' β' V₀' V₁' h₀' h₁' Q₀ Q₁)
                    (@DomainTheory.NeighbourhoodSystems.sumMap α β α' β' V₀ V₁ V₀' V₁' h₀ h₁ h₀' h₁' f g))
            (@And.intro
              (And
                (And
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
                (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  {h₀ :
                    ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                  {h₁ :
                    ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) α
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₀
                    (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁)))
              (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                {h₀ :
                  ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                {h₁ :
                  ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) β
                  (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                  (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₁
                  (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁))
              (@And.intro
                (And
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)))
                (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                  {h₀ :
                    ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                  {h₁ :
                    ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                  (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                  (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                  @DomainTheory.NeighbourhoodSystems.ComputableMap (Option (Sum α β)) α
                    (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                    (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁) P₀
                    (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁))
                (@And.intro
                  (And
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)))
                  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                    {h₀ :
                      ∀ (X : Set α),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                    {h₁ :
                      ∀ (Y : Set β),
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                    @DomainTheory.NeighbourhoodSystems.ComputableMap β (Option (Sum α β)) V₁
                      (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₁
                      (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                      (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁))
                  (@And.intro
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Option (Sum α β))
                            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
                    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
                      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
                      {h₀ :
                        ∀ (X : Set α),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
                      {h₁ :
                        ∀ (Y : Set β),
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
                      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
                      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁),
                      @DomainTheory.NeighbourhoodSystems.ComputableMap α (Option (Sum α β)) V₀
                        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) P₀
                        (@DomainTheory.NeighbourhoodSystems.sumPresentation α β V₀ V₁ h₀ h₁ P₀ P₁)
                        (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁))
                    @DomainTheory.NeighbourhoodSystems.sum_isEffectivelyGiven
                    @DomainTheory.NeighbourhoodSystems.inMap₀_isComputable)
                  @DomainTheory.NeighbourhoodSystems.inMap₁_isComputable)
                @DomainTheory.NeighbourhoodSystems.outMap₀_isComputable)
              @DomainTheory.NeighbourhoodSystems.outMap₁_isComputable)
            @DomainTheory.NeighbourhoodSystems.sumMap_isComputable)
          @DomainTheory.NeighbourhoodSystems.paired_isComputable)
        @DomainTheory.NeighbourhoodSystems.prodMap_isComputable)
      @DomainTheory.NeighbourhoodSystems.prod_isEffectivelyGiven)
    @DomainTheory.NeighbourhoodSystems.proj₀_isComputable)
  @DomainTheory.NeighbourhoodSystems.proj₁_isComputable

end DomainTheory.NeighbourhoodSystems
