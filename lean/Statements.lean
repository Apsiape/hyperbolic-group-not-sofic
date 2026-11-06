import Approx252
import NonSofic
set_option autoImplicit false
set_option maxRecDepth 100000

namespace PaperStatements

section
/-- Theorem 1.1 (v1.0). Original: `Approx252.exists_torsionFree_wordHyperbolic_not_sofic`. -/
def theorem_1_1 : Prop :=
  @Exists.{2} Type fun (G : Type) =>
  @Exists.{1} (Group.{0} G) fun (x : Group.{0} G) =>
    And (@OAI.Release075.TorsionFree.{0} G x)
      (And (@OAI.Release075.WordHyperbolic.{0} G x) (Not (@Approx252.IsSofic.{0} G x)))
end

section
universe u_1
/-- Theorem 3.1 (thm:ineq). Original: `NonSofic.presentation_ineq`. -/
def theorem_3_1 : Prop :=
  ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r) {Ω : Type u_1}
  [inst_1 : Fintype.{u_1} Ω] [inst_2 : DecidableEq.{u_1 + 1} Ω] (hq : @LT.lt.{0} Nat instLTNat r q)
  (σ :
    @OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
        (@OAI.Release075.MarkedLineData.presentation q r inst d hr) →
      Equiv.Perm.{u_1 + 1} Ω)
  (e : Nat) (hrect : @NonSofic.RectFix.{u_1} q r inst d hr Ω inst_1 inst_2 σ e)
  (he :
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        e)
      (@Fintype.card.{u_1} Ω inst_1)),
  @LE.le.{0} Nat instLENat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@Fintype.card.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.labelFintype q r inst d))
        r)
      (@Fintype.card.{u_1} Ω inst_1))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r
              (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → ZMod q)
                (@OAI.Release075.MarkedLineData.exceptional q r inst d)))))
        (@Fintype.card.{u_1} Ω inst_1))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@Finset.sum.{0, 0} (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) Nat Nat.instAddCommMonoid
          (@Finset.univ.{0} (@OAI.Release075.MarkedLineData.BlockIndex q r inst d)
            (@instFintypeProd.{0, 0} (@OAI.Release075.MarkedLineData.Regular q r inst d) Bool
              (@OAI.Release075.MarkedLineData.instFintypeRegular q r inst d) Bool.fintype))
          fun (b : @OAI.Release075.MarkedLineData.BlockIndex q r inst d) =>
          @Finset.sum.{0, 0}
            (@Subtype.{1} (@OAI.Release075.MarkedLineData.Label q r inst d)
              fun (x : @OAI.Release075.MarkedLineData.Label q r inst d) =>
              @Membership.mem.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r inst d))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r inst d))
                  (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@Finset.instSetLike.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)))
                (@OAI.Release075.CartesianBlock.labels.{0} (@OAI.Release075.MarkedLineData.Label q r inst d) r
                  (@OAI.Release075.MarkedLineData.block q r inst d hr b))
                x)
            Nat Nat.instAddCommMonoid
            (@Finset.univ.{0}
              (@Subtype.{1} (@OAI.Release075.MarkedLineData.Label q r inst d)
                fun (x : @OAI.Release075.MarkedLineData.Label q r inst d) =>
                @Membership.mem.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r inst d))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r inst d))
                    (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@Finset.instSetLike.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)))
                  (@OAI.Release075.CartesianBlock.labels.{0} (@OAI.Release075.MarkedLineData.Label q r inst d) r
                    (@OAI.Release075.MarkedLineData.block q r inst d hr b))
                  x)
              (@Finset.Subtype.fintype.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.CartesianBlock.labels.{0} (@OAI.Release075.MarkedLineData.Label q r inst d) r
                  (@OAI.Release075.MarkedLineData.block q r inst d hr b))))
            fun
              (i :
                @Subtype.{1} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  fun (x : @OAI.Release075.MarkedLineData.Label q r inst d) =>
                  @Membership.mem.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r inst d))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r inst d))
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@Finset.instSetLike.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)))
                    (@OAI.Release075.CartesianBlock.labels.{0} (@OAI.Release075.MarkedLineData.Label q r inst d) r
                      (@OAI.Release075.MarkedLineData.block q r inst d hr b))
                    x) =>
            @Finset.sum.{0, 0} (Fin r) Nat Nat.instAddCommMonoid (@Finset.univ.{0} (Fin r) (Fin.fintype r))
              fun (u : Fin r) =>
              @Finset.sum.{0, 0} (Fin r) Nat Nat.instAddCommMonoid (@Finset.univ.{0} (Fin r) (Fin.fintype r))
                fun (v : Fin r) => @NonSofic.triangleSupport.{u_1} q r inst d hr Ω inst_1 inst_2 σ b i u v)))
end

section
universe u_1
/-- Theorem 1.2, general constant. Original: `NonSofic.presentation_quant`. -/
def theorem_1_2_general : Prop :=
  ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r) {Ω : Type u_1}
  [inst_1 : Fintype.{u_1} Ω] [inst_2 : DecidableEq.{u_1 + 1} Ω] (hq : @LT.lt.{0} Nat instLTNat r q)
  (σ :
    @OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
        (@OAI.Release075.MarkedLineData.presentation q r inst d hr) →
      Equiv.Perm.{u_1 + 1} Ω)
  (e k : Nat) (hrect : @NonSofic.RectFix.{u_1} q r inst d hr Ω inst_1 inst_2 σ e)
  (he :
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        e)
      (@Fintype.card.{u_1} Ω inst_1))
  (hk :
    ∀ (b : @OAI.Release075.MarkedLineData.BlockIndex q r inst d)
      (i :
        @Subtype.{1} (@OAI.Release075.MarkedLineData.Label q r inst d)
          fun (x : @OAI.Release075.MarkedLineData.Label q r inst d) =>
          @Membership.mem.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r inst d))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r inst d))
              (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@Finset.instSetLike.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)))
            (@OAI.Release075.CartesianBlock.labels.{0} (@OAI.Release075.MarkedLineData.Label q r inst d) r
              (@OAI.Release075.MarkedLineData.block q r inst d hr b))
            x)
      (u v : Fin r),
      @LE.le.{0} Nat instLENat (@NonSofic.triangleSupport.{u_1} q r inst d hr Ω inst_1 inst_2 σ b i u v) k)
  (hk' :
    @LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) r
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@Fintype.card.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.labelFintype q r inst d)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        k)
      (@Fintype.card.{u_1} Ω inst_1)),
  False
end

section
/-- Theorem 1.2, Lemma 2.2 data. Original: `NonSofic.quant_lemma22`. -/
def theorem_1_2_lemma22 : Prop :=
  @Exists.{1} Nat fun (q : Nat) =>
  @Exists.{1} Nat fun (r : Nat) =>
    @Exists.{0} (Nat.Prime q) fun (hq : Nat.Prime q) =>
      have x : Fact (Nat.Prime q) := @Fact.mk (Nat.Prime q) hq;
      And
        (@Eq.{1} Nat r
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
              (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))
        (And (@LT.lt.{0} Nat instLTNat r q)
          (@Exists.{2} (@OAI.Release075.MarkedLineData q r x) fun (d : @OAI.Release075.MarkedLineData q r x) =>
            @Exists.{0} (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r)
              fun (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r) =>
              ∀ (Ω : Type) [inst : Fintype.{0} Ω] [inst_1 : DecidableEq.{1} Ω]
                (σ :
                  @OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                      (@OAI.Release075.MarkedLineData.presentation q r x d hr) →
                    Equiv.Perm.{1} Ω)
                (e k : Nat),
                @NonSofic.RectFix.{0} q r x d hr Ω inst inst_1 σ e →
                  @LE.le.{0} Nat instLENat
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        e)
                      (@Fintype.card.{0} Ω inst) →
                    @LT.lt.{0} Nat instLTNat
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) r)
                            q)
                          k)
                        (@Fintype.card.{0} Ω inst) →
                      @Exists.{1} (@OAI.Release075.MarkedLineData.BlockIndex q r x d)
                        fun (b : @OAI.Release075.MarkedLineData.BlockIndex q r x d) =>
                        @Exists.{1}
                          (@Subtype.{1} (@OAI.Release075.MarkedLineData.Label q r x d)
                            fun (x_1 : @OAI.Release075.MarkedLineData.Label q r x d) =>
                            @Membership.mem.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                              (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r x d))
                              (@SetLike.instMembership.{0, 0}
                                (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r x d))
                                (@OAI.Release075.MarkedLineData.Label q r x d)
                                (@Finset.instSetLike.{0} (@OAI.Release075.MarkedLineData.Label q r x d)))
                              (@OAI.Release075.CartesianBlock.labels.{0} (@OAI.Release075.MarkedLineData.Label q r x d)
                                r (@OAI.Release075.MarkedLineData.block q r x d hr b))
                              x_1)
                          fun
                            (i :
                              @Subtype.{1} (@OAI.Release075.MarkedLineData.Label q r x d)
                                fun (x_1 : @OAI.Release075.MarkedLineData.Label q r x d) =>
                                @Membership.mem.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                                  (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r x d))
                                  (@SetLike.instMembership.{0, 0}
                                    (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r x d))
                                    (@OAI.Release075.MarkedLineData.Label q r x d)
                                    (@Finset.instSetLike.{0} (@OAI.Release075.MarkedLineData.Label q r x d)))
                                  (@OAI.Release075.CartesianBlock.labels.{0}
                                    (@OAI.Release075.MarkedLineData.Label q r x d) r
                                    (@OAI.Release075.MarkedLineData.block q r x d hr b))
                                  x_1) =>
                          @Exists.{1} (Fin r) fun (u : Fin r) =>
                            @Exists.{1} (Fin r) fun (v : Fin r) =>
                              @LT.lt.{0} Nat instLTNat k
                                (@NonSofic.triangleSupport.{0} q r x d hr Ω inst inst_1 σ b i u v)))
end

section
universe u
/-- Corollary 1.3, universal word. Original: `NonSofic.exists_rect_word_killed_by_sofic_univ`. -/
def corollary_1_3_word : Prop :=
  ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r)
  (hq : @LT.lt.{0} Nat instLTNat r q),
  @Exists.{1} (@NonSofic.RectIndex q r inst d) fun (x : @NonSofic.RectIndex q r inst d) =>
    And (@Eq.{1} (@NonSofic.RectIndex q r inst d) x (@NonSofic.residualWitness q r inst d hr hq))
      (And
        (@Ne.{1}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@NonSofic.rectWord q r inst d hr x)
          (@OfNat.ofNat.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (nat_lit 1)
            (@One.toOfNat1.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@InvOneClass.toOne.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@DivInvOneMonoid.toInvOneClass.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@DivisionMonoid.toDivInvOneMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@Group.toDivisionMonoid.{0}
                      (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@instGroupPresentedGroup.{0}
                        (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                        (@OAI.Release075.BlockPresentation.relators.{0, 0}
                          (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))))))))
        (∀ (H : Type u) [inst_1 : Group.{u} H],
          @Approx252.IsSofic.{u} H inst_1 →
            ∀
              (π :
                @MonoidHom.{0, u}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  H
                  (@MulOneClass.toMulOne.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@Monoid.toMulOneClass.{0}
                      (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@DivInvMonoid.toMonoid.{0}
                        (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                          (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                        (@Group.toDivInvMonoid.{0}
                          (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                            (@OAI.Release075.MarkedLineData.Label q r inst d)
                            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                          (@instGroupPresentedGroup.{0}
                            (@OAI.Release075.BlockPresentation.Edge.{0, 0}
                              (@OAI.Release075.MarkedLineData.Label q r inst d)
                              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                            (@OAI.Release075.BlockPresentation.relators.{0, 0}
                              (@OAI.Release075.MarkedLineData.Label q r inst d)
                              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                              (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
                  (@MulOneClass.toMulOne.{u} H
                    (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst_1))))),
              @Eq.{u + 1} H
                (@DFunLike.coe.{u + 1, 1, u + 1}
                  (@MonoidHom.{0, u}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    H
                    (@MulOneClass.toMulOne.{0}
                      (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@Monoid.toMulOneClass.{0}
                        (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                          (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                        (@DivInvMonoid.toMonoid.{0}
                          (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                            (@OAI.Release075.MarkedLineData.Label q r inst d)
                            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                          (@Group.toDivInvMonoid.{0}
                            (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                              (@OAI.Release075.MarkedLineData.Label q r inst d)
                              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                            (@instGroupPresentedGroup.{0}
                              (@OAI.Release075.BlockPresentation.Edge.{0, 0}
                                (@OAI.Release075.MarkedLineData.Label q r inst d)
                                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                              (@OAI.Release075.BlockPresentation.relators.{0, 0}
                                (@OAI.Release075.MarkedLineData.Label q r inst d)
                                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                                (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
                    (@MulOneClass.toMulOne.{u} H
                      (@Monoid.toMulOneClass.{u} H
                        (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst_1)))))
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (fun
                      (x :
                        @OAI.Release075.BlockPresentation.GroupType.{0, 0}
                          (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr)) =>
                    H)
                  (@MonoidHom.instFunLike.{0, u}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    H
                    (@MulOneClass.toMulOne.{0}
                      (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@Monoid.toMulOneClass.{0}
                        (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                          (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                        (@DivInvMonoid.toMonoid.{0}
                          (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                            (@OAI.Release075.MarkedLineData.Label q r inst d)
                            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                          (@Group.toDivInvMonoid.{0}
                            (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                              (@OAI.Release075.MarkedLineData.Label q r inst d)
                              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                            (@instGroupPresentedGroup.{0}
                              (@OAI.Release075.BlockPresentation.Edge.{0, 0}
                                (@OAI.Release075.MarkedLineData.Label q r inst d)
                                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                              (@OAI.Release075.BlockPresentation.relators.{0, 0}
                                (@OAI.Release075.MarkedLineData.Label q r inst d)
                                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                                (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
                    (@MulOneClass.toMulOne.{u} H
                      (@Monoid.toMulOneClass.{u} H
                        (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst_1)))))
                  π (@NonSofic.rectWord q r inst d hr x))
                (@OfNat.ofNat.{u} H (nat_lit 1)
                  (@One.toOfNat1.{u} H
                    (@InvOneClass.toOne.{u} H
                      (@DivInvOneMonoid.toInvOneClass.{u} H
                        (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst_1))))))))
end

section
universe u_1
/-- Corollary 1.3, quotient. Original: `NonSofic.quotient_not_sofic`. -/
def corollary_1_3_quotient : Prop :=
  ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r)
  (hq : @LT.lt.{0} Nat instLTNat r q) {H : Type u_1} [inst_1 : Group.{u_1} H]
  (π :
    @MonoidHom.{0, u_1}
      (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
      H
      (@MulOneClass.toMulOne.{0}
        (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
        (@Monoid.toMulOneClass.{0}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@DivInvMonoid.toMonoid.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@Group.toDivInvMonoid.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@instGroupPresentedGroup.{0}
                (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
      (@MulOneClass.toMulOne.{u_1} H
        (@Monoid.toMulOneClass.{u_1} H (@DivInvMonoid.toMonoid.{u_1} H (@Group.toDivInvMonoid.{u_1} H inst_1)))))
  (hπ :
    ∀ (x : @NonSofic.RectIndex q r inst d),
      @Ne.{u_1 + 1} H
        (@DFunLike.coe.{u_1 + 1, 1, u_1 + 1}
          (@MonoidHom.{0, u_1}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            H
            (@MulOneClass.toMulOne.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Monoid.toMulOneClass.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@DivInvMonoid.toMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@Group.toDivInvMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@instGroupPresentedGroup.{0}
                      (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@OAI.Release075.BlockPresentation.relators.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
            (@MulOneClass.toMulOne.{u_1} H
              (@Monoid.toMulOneClass.{u_1} H (@DivInvMonoid.toMonoid.{u_1} H (@Group.toDivInvMonoid.{u_1} H inst_1)))))
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (fun
              (x :
                @OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr)) =>
            H)
          (@MonoidHom.instFunLike.{0, u_1}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            H
            (@MulOneClass.toMulOne.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Monoid.toMulOneClass.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@DivInvMonoid.toMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@Group.toDivInvMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@instGroupPresentedGroup.{0}
                      (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@OAI.Release075.BlockPresentation.relators.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
            (@MulOneClass.toMulOne.{u_1} H
              (@Monoid.toMulOneClass.{u_1} H (@DivInvMonoid.toMonoid.{u_1} H (@Group.toDivInvMonoid.{u_1} H inst_1)))))
          π (@NonSofic.rectWord q r inst d hr x))
        (@OfNat.ofNat.{u_1} H (nat_lit 1)
          (@One.toOfNat1.{u_1} H
            (@InvOneClass.toOne.{u_1} H
              (@DivInvOneMonoid.toInvOneClass.{u_1} H
                (@DivisionMonoid.toDivInvOneMonoid.{u_1} H (@Group.toDivisionMonoid.{u_1} H inst_1))))))),
  Not (@Approx252.IsSofic.{u_1} H inst_1)
end

section
/-- Lemma 6.2. Original: `NonSofic.LineFree.lineSubgroup_free`. -/
def lemma_6_2 : Prop :=
  ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r)
  (i : @OAI.Release075.MarkedLineData.Label q r inst d),
  @Function.Injective.{1, 1}
    (FreeGroup.{0}
      (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
        @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
          (@Prod.mk.{0, 0} (Fin r) (Fin r) (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
    (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
    (@DFunLike.coe.{1, 1, 1}
      (@MonoidHom.{0, 0}
        (FreeGroup.{0}
          (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
            @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
              (@Prod.mk.{0, 0} (Fin r) (Fin r)
                (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
        (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
        (@MulOneClass.toMulOne.{0}
          (FreeGroup.{0}
            (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
              @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                (@Prod.mk.{0, 0} (Fin r) (Fin r)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
          (@Monoid.toMulOneClass.{0}
            (FreeGroup.{0}
              (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                  (@Prod.mk.{0, 0} (Fin r) (Fin r)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
            (@DivInvMonoid.toMonoid.{0}
              (FreeGroup.{0}
                (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
              (@Group.toDivInvMonoid.{0}
                (FreeGroup.{0}
                  (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                    @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                      (@Prod.mk.{0, 0} (Fin r) (Fin r)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                (@FreeGroup.instGroup.{0}
                  (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                    @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                      (@Prod.mk.{0, 0} (Fin r) (Fin r)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))))))
        (@MulOneClass.toMulOne.{0}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@Monoid.toMulOneClass.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@DivInvMonoid.toMonoid.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Group.toDivInvMonoid.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@instGroupPresentedGroup.{0}
                  (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))))))
      (FreeGroup.{0}
        (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
          @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
            (@Prod.mk.{0, 0} (Fin r) (Fin r)
              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
      (fun
          (x :
            FreeGroup.{0}
              (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                  (@Prod.mk.{0, 0} (Fin r) (Fin r)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)))) =>
        @OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
      (@MonoidHom.instFunLike.{0, 0}
        (FreeGroup.{0}
          (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
            @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
              (@Prod.mk.{0, 0} (Fin r) (Fin r)
                (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
        (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
        (@MulOneClass.toMulOne.{0}
          (FreeGroup.{0}
            (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
              @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                (@Prod.mk.{0, 0} (Fin r) (Fin r)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
          (@Monoid.toMulOneClass.{0}
            (FreeGroup.{0}
              (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                  (@Prod.mk.{0, 0} (Fin r) (Fin r)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
            (@DivInvMonoid.toMonoid.{0}
              (FreeGroup.{0}
                (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
              (@Group.toDivInvMonoid.{0}
                (FreeGroup.{0}
                  (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                    @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                      (@Prod.mk.{0, 0} (Fin r) (Fin r)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                (@FreeGroup.instGroup.{0}
                  (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                    @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                      (@Prod.mk.{0, 0} (Fin r) (Fin r)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))))))
        (@MulOneClass.toMulOne.{0}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@Monoid.toMulOneClass.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@DivInvMonoid.toMonoid.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Group.toDivInvMonoid.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@instGroupPresentedGroup.{0}
                  (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))))))
      (@DFunLike.coe.{1, 1, 1}
        (Equiv.{1, 1}
          ((@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
              @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                (@Prod.mk.{0, 0} (Fin r) (Fin r)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))) →
            @OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@MonoidHom.{0, 0}
            (FreeGroup.{0}
              (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                  (@Prod.mk.{0, 0} (Fin r) (Fin r)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@MulOneClass.toMulOne.{0}
              (FreeGroup.{0}
                (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
              (@Monoid.toMulOneClass.{0}
                (FreeGroup.{0}
                  (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                    @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                      (@Prod.mk.{0, 0} (Fin r) (Fin r)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                (@DivInvMonoid.toMonoid.{0}
                  (FreeGroup.{0}
                    (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                      @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                        (@Prod.mk.{0, 0} (Fin r) (Fin r)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                  (@Group.toDivInvMonoid.{0}
                    (FreeGroup.{0}
                      (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                        @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                          (@Prod.mk.{0, 0} (Fin r) (Fin r)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                    (@FreeGroup.instGroup.{0}
                      (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                        @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                          (@Prod.mk.{0, 0} (Fin r) (Fin r)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))))))
            (@MulOneClass.toMulOne.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Monoid.toMulOneClass.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@DivInvMonoid.toMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@Group.toDivInvMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@instGroupPresentedGroup.{0}
                      (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@OAI.Release075.BlockPresentation.relators.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))))
        ((@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
            @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
              (@Prod.mk.{0, 0} (Fin r) (Fin r)
                (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))) →
          @OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
        (fun
            (x :
              (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))) →
                @OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr)) =>
          @MonoidHom.{0, 0}
            (FreeGroup.{0}
              (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                  (@Prod.mk.{0, 0} (Fin r) (Fin r)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@MulOneClass.toMulOne.{0}
              (FreeGroup.{0}
                (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
              (@Monoid.toMulOneClass.{0}
                (FreeGroup.{0}
                  (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                    @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                      (@Prod.mk.{0, 0} (Fin r) (Fin r)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                (@DivInvMonoid.toMonoid.{0}
                  (FreeGroup.{0}
                    (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                      @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                        (@Prod.mk.{0, 0} (Fin r) (Fin r)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                  (@Group.toDivInvMonoid.{0}
                    (FreeGroup.{0}
                      (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                        @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                          (@Prod.mk.{0, 0} (Fin r) (Fin r)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                    (@FreeGroup.instGroup.{0}
                      (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                        @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                          (@Prod.mk.{0, 0} (Fin r) (Fin r)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))))))
            (@MulOneClass.toMulOne.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Monoid.toMulOneClass.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@DivInvMonoid.toMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@Group.toDivInvMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@instGroupPresentedGroup.{0}
                      (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@OAI.Release075.BlockPresentation.relators.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))))))
        (@EquivLike.toFunLike.{1, 1, 1}
          (Equiv.{1, 1}
            ((@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                  (@Prod.mk.{0, 0} (Fin r) (Fin r)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))) →
              @OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@MonoidHom.{0, 0}
              (FreeGroup.{0}
                (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0}
                  (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                    @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                      (@Prod.mk.{0, 0} (Fin r) (Fin r)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0}
                    (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                      @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                        (@Prod.mk.{0, 0} (Fin r) (Fin r)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0}
                      (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                        @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                          (@Prod.mk.{0, 0} (Fin r) (Fin r)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0}
                        (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                          @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                            (@Prod.mk.{0, 0} (Fin r) (Fin r)
                              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                      (@FreeGroup.instGroup.{0}
                        (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                          @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                            (@Prod.mk.{0, 0} (Fin r) (Fin r)
                              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))))))
              (@MulOneClass.toMulOne.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@Monoid.toMulOneClass.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@DivInvMonoid.toMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@Group.toDivInvMonoid.{0}
                      (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@instGroupPresentedGroup.{0}
                        (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                        (@OAI.Release075.BlockPresentation.relators.{0, 0}
                          (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))))
          ((@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
              @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                (@Prod.mk.{0, 0} (Fin r) (Fin r)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))) →
            @OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@MonoidHom.{0, 0}
            (FreeGroup.{0}
              (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                  (@Prod.mk.{0, 0} (Fin r) (Fin r)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@MulOneClass.toMulOne.{0}
              (FreeGroup.{0}
                (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
              (@Monoid.toMulOneClass.{0}
                (FreeGroup.{0}
                  (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                    @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                      (@Prod.mk.{0, 0} (Fin r) (Fin r)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                (@DivInvMonoid.toMonoid.{0}
                  (FreeGroup.{0}
                    (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                      @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                        (@Prod.mk.{0, 0} (Fin r) (Fin r)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                  (@Group.toDivInvMonoid.{0}
                    (FreeGroup.{0}
                      (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                        @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                          (@Prod.mk.{0, 0} (Fin r) (Fin r)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                    (@FreeGroup.instGroup.{0}
                      (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                        @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                          (@Prod.mk.{0, 0} (Fin r) (Fin r)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))))))
            (@MulOneClass.toMulOne.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Monoid.toMulOneClass.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@DivInvMonoid.toMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@Group.toDivInvMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@instGroupPresentedGroup.{0}
                      (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@OAI.Release075.BlockPresentation.relators.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))))))
          (@Equiv.instEquivLike.{1, 1}
            ((@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                  (@Prod.mk.{0, 0} (Fin r) (Fin r)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                    (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))) →
              @OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@MonoidHom.{0, 0}
              (FreeGroup.{0}
                (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@MulOneClass.toMulOne.{0}
                (FreeGroup.{0}
                  (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                    @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                      (@Prod.mk.{0, 0} (Fin r) (Fin r)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                        (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                (@Monoid.toMulOneClass.{0}
                  (FreeGroup.{0}
                    (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                      @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                        (@Prod.mk.{0, 0} (Fin r) (Fin r)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                          (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                  (@DivInvMonoid.toMonoid.{0}
                    (FreeGroup.{0}
                      (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                        @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                          (@Prod.mk.{0, 0} (Fin r) (Fin r)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                            (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                    (@Group.toDivInvMonoid.{0}
                      (FreeGroup.{0}
                        (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                          @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                            (@Prod.mk.{0, 0} (Fin r) (Fin r)
                              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))
                      (@FreeGroup.instGroup.{0}
                        (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                          @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                            (@Prod.mk.{0, 0} (Fin r) (Fin r)
                              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))))))))
              (@MulOneClass.toMulOne.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@Monoid.toMulOneClass.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@DivInvMonoid.toMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@Group.toDivInvMonoid.{0}
                      (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@instGroupPresentedGroup.{0}
                        (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                        (@OAI.Release075.BlockPresentation.relators.{0, 0}
                          (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))))))))
        (@FreeGroup.lift.{0, 0}
          (@Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
            @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
              (@Prod.mk.{0, 0} (Fin r) (Fin r)
                (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)))
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@instGroupPresentedGroup.{0}
            (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))
        fun
          (p :
            @Subtype.{1} (Prod.{0, 0} (Fin r) (Fin r)) fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
              @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                (@Prod.mk.{0, 0} (Fin r) (Fin r)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                  (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr))) =>
        @HMul.hMul.{0, 0, 0}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@instHMul.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@MulOne.toMul.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@MulOneClass.toMulOne.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@Monoid.toMulOneClass.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@DivInvMonoid.toMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@Group.toDivInvMonoid.{0}
                      (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@instGroupPresentedGroup.{0}
                        (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                        (@OAI.Release075.BlockPresentation.relators.{0, 0}
                          (@OAI.Release075.MarkedLineData.Label q r inst d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                          (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))))
          (@OAI.Release075.BlockPresentation.x.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr) i
            (@Prod.fst.{0, 0} (Fin r) (Fin r)
              (@Subtype.val.{1} (Prod.{0, 0} (Fin r) (Fin r))
                (fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)))
                p))
            (@Prod.snd.{0, 0} (Fin r) (Fin r)
              (@Subtype.val.{1} (Prod.{0, 0} (Fin r) (Fin r))
                (fun (p : Prod.{0, 0} (Fin r) (Fin r)) =>
                  @Ne.{1} (Prod.{0, 0} (Fin r) (Fin r)) p
                    (@Prod.mk.{0, 0} (Fin r) (Fin r)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
                      (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)))
                p)))
          (@Inv.inv.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@InvOneClass.toInv.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@DivInvOneMonoid.toInvOneClass.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@DivisionMonoid.toDivInvOneMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@Group.toDivisionMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@instGroupPresentedGroup.{0}
                      (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@OAI.Release075.BlockPresentation.relators.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
            (@OAI.Release075.BlockPresentation.x.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr) i
              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)
              (@Fin.mk r (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hr)))))
end

section
universe u_1
/-- Theorem 6.1. Original: `NonSofic.collapse`. -/
def theorem_6_1 : Prop :=
  ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r) {R : Type u_1}
  [inst_1 : Ring.{u_1} R] (ρ : @NonSofic.RankFn.{u_1} R inst_1)
  (c :
    @RingHom.{0, u_1} (ZMod q) R
      (@Semiring.toNonAssocSemiring.{0} (ZMod q)
        (@CommSemiring.toSemiring.{0} (ZMod q)
          (@Semifield.toCommSemiring.{0} (ZMod q) (@Field.toSemifield.{0} (ZMod q) (@ZMod.instField q inst)))))
      (@Semiring.toNonAssocSemiring.{u_1} R (@Ring.toSemiring.{u_1} R inst_1)))
  (χ :
    @MonoidHom.{0, u_1}
      (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
      R
      (@MulOneClass.toMulOne.{0}
        (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
        (@Monoid.toMulOneClass.{0}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@DivInvMonoid.toMonoid.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@Group.toDivInvMonoid.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@instGroupPresentedGroup.{0}
                (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
      (@MulOneClass.toMulOne.{u_1} R
        (@MulZeroOneClass.toMulOneClass.{u_1} R
          (@instMulZeroOneClassOfSemiring.{u_1} R (@Ring.toSemiring.{u_1} R inst_1))))),
  And
    (@LE.le.{0} Real Real.instLE
      (@Finset.sum.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d) Real Real.instAddCommMonoid
        (@Finset.univ.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.labelFintype q r inst d))
        fun (i : @OAI.Release075.MarkedLineData.Label q r inst d) =>
        @NonSofic.RankFn.rk.{u_1} R inst_1 ρ (Fin r) (Fin r) (Fin.fintype r) (Fin.fintype r) (instDecidableEqFin r)
          (instDecidableEqFin r) (@NonSofic.lineMatrix.{u_1} q r inst d hr R inst_1 χ i))
      (@Nat.cast.{0} Real Real.instNatCast
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
              (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → ZMod q)
                (@OAI.Release075.MarkedLineData.exceptional q r inst d))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r
            (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → ZMod q)
              (@OAI.Release075.MarkedLineData.exceptional q r inst d))))))
    (@LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
              (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → ZMod q)
                (@OAI.Release075.MarkedLineData.exceptional q r inst d))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r
            (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → ZMod q)
              (@OAI.Release075.MarkedLineData.exceptional q r inst d)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@Fintype.card.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.labelFintype q r inst d))
        r))
end

section
universe u_1
/-- Theorem 6.1, group ring. Original: `NonSofic.collapse_groupRing`. -/
def theorem_6_1_groupRing : Prop :=
  ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r) (K : Type u_1)
  [inst_1 : DivisionRing.{u_1} K]
  [@CharP.{u_1} K
      (@AddGroupWithOne.toAddMonoidWithOne.{u_1} K
        (@Ring.toAddGroupWithOne.{u_1} K (@DivisionRing.toRing.{u_1} K inst_1)))
      q]
  (ρ :
    @NonSofic.RankFn.{u_1}
      (@MonoidAlgebra.{u_1, 0} K
        (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
        (@Ring.toSemiring.{u_1} K (@DivisionRing.toRing.{u_1} K inst_1)))
      (@MonoidAlgebra.ring.{u_1, 0} K
        (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
        (@DivisionRing.toRing.{u_1} K inst_1)
        (@DivInvMonoid.toMonoid.{0}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@Group.toDivInvMonoid.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@instGroupPresentedGroup.{0}
              (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))))),
  And
    (@LE.le.{0} Real Real.instLE
      (@Finset.sum.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d) Real Real.instAddCommMonoid
        (@Finset.univ.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.labelFintype q r inst d))
        fun (i : @OAI.Release075.MarkedLineData.Label q r inst d) =>
        @NonSofic.RankFn.rk.{u_1}
          (@MonoidAlgebra.{u_1, 0} K
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@Ring.toSemiring.{u_1} K (@DivisionRing.toRing.{u_1} K inst_1)))
          (@MonoidAlgebra.ring.{u_1, 0} K
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@DivisionRing.toRing.{u_1} K inst_1)
            (@DivInvMonoid.toMonoid.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Group.toDivInvMonoid.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@instGroupPresentedGroup.{0}
                  (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))))
          ρ (Fin r) (Fin r) (Fin.fintype r) (Fin.fintype r) (instDecidableEqFin r) (instDecidableEqFin r)
          (@NonSofic.lineMatrix.{u_1} q r inst d hr
            (@MonoidAlgebra.{u_1, 0} K
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Ring.toSemiring.{u_1} K (@DivisionRing.toRing.{u_1} K inst_1)))
            (@MonoidAlgebra.ring.{u_1, 0} K
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@DivisionRing.toRing.{u_1} K inst_1)
              (@DivInvMonoid.toMonoid.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@Group.toDivInvMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@instGroupPresentedGroup.{0}
                    (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))))))
            (@MonoidAlgebra.of.{u_1, 0} K
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@Ring.toSemiring.{u_1} K (@DivisionRing.toRing.{u_1} K inst_1))
              (@Monoid.toMulOneClass.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@DivInvMonoid.toMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@Group.toDivInvMonoid.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                      (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@instGroupPresentedGroup.{0}
                      (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                      (@OAI.Release075.BlockPresentation.relators.{0, 0}
                        (@OAI.Release075.MarkedLineData.Label q r inst d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                        (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
            i))
      (@Nat.cast.{0} Real Real.instNatCast
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
              (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → ZMod q)
                (@OAI.Release075.MarkedLineData.exceptional q r inst d))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r
            (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → ZMod q)
              (@OAI.Release075.MarkedLineData.exceptional q r inst d))))))
    (@LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
              (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → ZMod q)
                (@OAI.Release075.MarkedLineData.exceptional q r inst d))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r
            (@Finset.card.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) → ZMod q)
              (@OAI.Release075.MarkedLineData.exceptional q r inst d)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@Fintype.card.{0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.labelFintype q r inst d))
        r))
end

section
universe u_1 u_2 u_3
/-- Lemma 6.3. Original: `NonSofic.isUnit_map_of_zQuotientData`. -/
def lemma_6_3 : Prop :=
  ∀ {K : Type u_1} [inst : Ring.{u_1} K] {Λ : Type u_2} [inst_1 : Group.{u_2} Λ] {D : Type u_3}
  [inst_2 : DivisionRing.{u_3} D]
  (φ :
    @RingHom.{max u_2 u_1, u_3} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) D
      (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
        (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
      (@Semiring.toNonAssocSemiring.{u_3} D (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst_2))))
  (Q : @NonSofic.ZQuotientData.{u_2} Λ inst_1) {r : Nat} (y : Fin r → Fin r → Λ)
  (hy :
    ∀ (u v : Fin r),
      @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
        (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ (@Subgroup.instSetLike.{u_2} Λ inst_1))
        (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) (y u v))
  (hδd :
    ∀ (u : Fin r),
      @Eq.{1} (Multiplicative.{0} Int)
        (@DFunLike.coe.{u_2 + 1, u_2 + 1, 1}
          (@MonoidHom.{u_2, 0}
            (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
              @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ (@Subgroup.instSetLike.{u_2} Λ inst_1))
                (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
            (Multiplicative.{0} Int)
            (@MulOneClass.toMulOne.{u_2}
              (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
                @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                  (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                    (@Subgroup.instSetLike.{u_2} Λ inst_1))
                  (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
              (@SubmonoidClass.toMulOneClass.{u_2, u_2} Λ
                (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1)))
                (@Subgroup.{u_2} Λ inst_1) (@Subgroup.instSetLike.{u_2} Λ inst_1)
                (@SubgroupClass.toSubmonoidClass.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                  (@Group.toDivInvMonoid.{u_2} Λ inst_1) (@Subgroup.instSetLike.{u_2} Λ inst_1)
                  (@Subgroup.instSubgroupClass.{u_2} Λ inst_1))
                (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q)))
            (@MulOneClass.toMulOne.{0} (Multiplicative.{0} Int)
              (@Multiplicative.mulOneClass.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))))
          (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
            @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
              (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ (@Subgroup.instSetLike.{u_2} Λ inst_1))
              (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
          (fun
              (x :
                @Subtype.{u_2 + 1} Λ fun (x : Λ) =>
                  @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                    (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                      (@Subgroup.instSetLike.{u_2} Λ inst_1))
                    (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x) =>
            Multiplicative.{0} Int)
          (@MonoidHom.instFunLike.{u_2, 0}
            (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
              @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ (@Subgroup.instSetLike.{u_2} Λ inst_1))
                (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
            (Multiplicative.{0} Int)
            (@MulOneClass.toMulOne.{u_2}
              (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
                @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                  (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                    (@Subgroup.instSetLike.{u_2} Λ inst_1))
                  (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
              (@SubmonoidClass.toMulOneClass.{u_2, u_2} Λ
                (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1)))
                (@Subgroup.{u_2} Λ inst_1) (@Subgroup.instSetLike.{u_2} Λ inst_1)
                (@SubgroupClass.toSubmonoidClass.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                  (@Group.toDivInvMonoid.{u_2} Λ inst_1) (@Subgroup.instSetLike.{u_2} Λ inst_1)
                  (@Subgroup.instSubgroupClass.{u_2} Λ inst_1))
                (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q)))
            (@MulOneClass.toMulOne.{0} (Multiplicative.{0} Int)
              (@Multiplicative.mulOneClass.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))))
          (@NonSofic.ZQuotientData.δ.{u_2} Λ inst_1 Q)
          (@Subtype.mk.{u_2 + 1} Λ
            (fun (x : Λ) =>
              @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ (@Subgroup.instSetLike.{u_2} Λ inst_1))
                (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
            (y u u) (hy u u)))
        (@OfNat.ofNat.{0} (Multiplicative.{0} Int) (nat_lit 1)
          (@One.toOfNat1.{0} (Multiplicative.{0} Int)
            (@instOneMultiplicativeOfZero.{0} Int
              (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))))))
  (hδo :
    ∀ (u v : Fin r),
      @Ne.{1} (Fin r) u v →
        @Eq.{1} (Multiplicative.{0} Int)
          (@DFunLike.coe.{u_2 + 1, u_2 + 1, 1}
            (@MonoidHom.{u_2, 0}
              (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
                @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                  (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                    (@Subgroup.instSetLike.{u_2} Λ inst_1))
                  (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
              (Multiplicative.{0} Int)
              (@MulOneClass.toMulOne.{u_2}
                (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
                  @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                    (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                      (@Subgroup.instSetLike.{u_2} Λ inst_1))
                    (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
                (@SubmonoidClass.toMulOneClass.{u_2, u_2} Λ
                  (@Monoid.toMulOneClass.{u_2} Λ
                    (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1)))
                  (@Subgroup.{u_2} Λ inst_1) (@Subgroup.instSetLike.{u_2} Λ inst_1)
                  (@SubgroupClass.toSubmonoidClass.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                    (@Group.toDivInvMonoid.{u_2} Λ inst_1) (@Subgroup.instSetLike.{u_2} Λ inst_1)
                    (@Subgroup.instSubgroupClass.{u_2} Λ inst_1))
                  (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q)))
              (@MulOneClass.toMulOne.{0} (Multiplicative.{0} Int)
                (@Multiplicative.mulOneClass.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))))
            (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
              @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ (@Subgroup.instSetLike.{u_2} Λ inst_1))
                (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
            (fun
                (x :
                  @Subtype.{u_2 + 1} Λ fun (x : Λ) =>
                    @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                      (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                        (@Subgroup.instSetLike.{u_2} Λ inst_1))
                      (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x) =>
              Multiplicative.{0} Int)
            (@MonoidHom.instFunLike.{u_2, 0}
              (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
                @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                  (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                    (@Subgroup.instSetLike.{u_2} Λ inst_1))
                  (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
              (Multiplicative.{0} Int)
              (@MulOneClass.toMulOne.{u_2}
                (@Subtype.{u_2 + 1} Λ fun (x : Λ) =>
                  @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                    (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                      (@Subgroup.instSetLike.{u_2} Λ inst_1))
                    (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
                (@SubmonoidClass.toMulOneClass.{u_2, u_2} Λ
                  (@Monoid.toMulOneClass.{u_2} Λ
                    (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1)))
                  (@Subgroup.{u_2} Λ inst_1) (@Subgroup.instSetLike.{u_2} Λ inst_1)
                  (@SubgroupClass.toSubmonoidClass.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                    (@Group.toDivInvMonoid.{u_2} Λ inst_1) (@Subgroup.instSetLike.{u_2} Λ inst_1)
                    (@Subgroup.instSubgroupClass.{u_2} Λ inst_1))
                  (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q)))
              (@MulOneClass.toMulOne.{0} (Multiplicative.{0} Int)
                (@Multiplicative.mulOneClass.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))))
            (@NonSofic.ZQuotientData.δ.{u_2} Λ inst_1 Q)
            (@Subtype.mk.{u_2 + 1} Λ
              (fun (x : Λ) =>
                @Membership.mem.{u_2, u_2} Λ (@Subgroup.{u_2} Λ inst_1)
                  (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} Λ inst_1) Λ
                    (@Subgroup.instSetLike.{u_2} Λ inst_1))
                  (@NonSofic.ZQuotientData.A.{u_2} Λ inst_1 Q) x)
              (y u v) (hy u v)))
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} Int (Multiplicative.{0} Int)) Int
            (fun (x : Int) => Multiplicative.{0} Int)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} Int (Multiplicative.{0} Int)) Int (Multiplicative.{0} Int)
              (@Equiv.instEquivLike.{1, 1} Int (Multiplicative.{0} Int)))
            (@Multiplicative.ofAdd.{0} Int)
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hind :
    @NonSofic.PowersLeftIndep.{u_3} D inst_2
      (@NonSofic.divClosure.{u_1, u_2, u_3} K inst Λ inst_1 D inst_2 φ (@NonSofic.ZQuotientData.A0.{u_2} Λ inst_1 Q))
      (@DFunLike.coe.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1), max (u_1 + 1) (u_2 + 1), u_3 + 1}
        (@RingHom.{max u_2 u_1, u_3} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) D
          (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
            (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
          (@Semiring.toNonAssocSemiring.{u_3} D (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst_2))))
        (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
        (fun (x : @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) => D)
        (@RingHom.instFunLike.{max u_1 u_2, u_3} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) D
          (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
            (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
          (@Semiring.toNonAssocSemiring.{u_3} D (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst_2))))
        φ
        (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, max (u_1 + 1) (u_2 + 1)}
          (@MonoidHom.{u_2, max u_2 u_1} Λ (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
            (@MulOneClass.toMulOne.{u_2} Λ
              (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
            (@MulOneClass.toMulOne.{max u_1 u_2} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
              (@MulZeroOneClass.toMulOneClass.{max u_1 u_2}
                (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                (@NonAssocSemiring.toMulZeroOneClass.{max u_1 u_2}
                  (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                  (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))))
          Λ (fun (x : Λ) => @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
          (@MonoidHom.instFunLike.{u_2, max u_1 u_2} Λ (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
            (@MulOneClass.toMulOne.{u_2} Λ
              (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
            (@MulOneClass.toMulOne.{max u_1 u_2} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
              (@MulZeroOneClass.toMulOneClass.{max u_1 u_2}
                (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                (@NonAssocSemiring.toMulZeroOneClass.{max u_1 u_2}
                  (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                  (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))))
          (@MonoidAlgebra.of.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
            (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
          (@NonSofic.ZQuotientData.t.{u_2} Λ inst_1 Q)))),
  @IsUnit.{u_3} (Matrix.{0, 0, u_3} (Fin r) (Fin r) D)
    (@Semiring.toMonoid.{u_3} (Matrix.{0, 0, u_3} (Fin r) (Fin r) D)
      (@Matrix.semiring.{u_3, 0} (Fin r) D (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst_2))
        (Fin.fintype r) (instDecidableEqFin r)))
    (@Matrix.map.{max u_1 u_2, u_3, 0, 0} (Fin r) (Fin r)
      (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) D
      (@DFunLike.coe.{max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1)}
        (Equiv.{max 1 ((max u_1 u_2) + 1), max ((max u_1 u_2) + 1) 1}
          (Fin r → Fin r → @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
          (Matrix.{0, 0, max u_1 u_2} (Fin r) (Fin r) (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))))
        (Fin r → Fin r → @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
        (fun (x : Fin r → Fin r → @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) =>
          Matrix.{0, 0, max u_1 u_2} (Fin r) (Fin r) (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)))
        (@EquivLike.toFunLike.{max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1)}
          (Equiv.{max 1 ((max u_1 u_2) + 1), max ((max u_1 u_2) + 1) 1}
            (Fin r → Fin r → @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
            (Matrix.{0, 0, max u_1 u_2} (Fin r) (Fin r)
              (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))))
          (Fin r → Fin r → @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
          (Matrix.{0, 0, max u_1 u_2} (Fin r) (Fin r) (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)))
          (@Equiv.instEquivLike.{max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1)}
            (Fin r → Fin r → @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
            (Matrix.{0, 0, max u_1 u_2} (Fin r) (Fin r)
              (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)))))
        (@Matrix.of.{max u_1 u_2, 0, 0} (Fin r) (Fin r) (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)))
        fun (u v : Fin r) =>
        @DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, max (u_1 + 1) (u_2 + 1)}
          (@MonoidHom.{u_2, max u_2 u_1} Λ (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
            (@MulOneClass.toMulOne.{u_2} Λ
              (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
            (@MulOneClass.toMulOne.{max u_1 u_2} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
              (@MulZeroOneClass.toMulOneClass.{max u_1 u_2}
                (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                (@NonAssocSemiring.toMulZeroOneClass.{max u_1 u_2}
                  (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                  (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))))
          Λ (fun (x : Λ) => @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
          (@MonoidHom.instFunLike.{u_2, max u_1 u_2} Λ (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
            (@MulOneClass.toMulOne.{u_2} Λ
              (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
            (@MulOneClass.toMulOne.{max u_1 u_2} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
              (@MulZeroOneClass.toMulOneClass.{max u_1 u_2}
                (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                (@NonAssocSemiring.toMulZeroOneClass.{max u_1 u_2}
                  (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                  (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))))
          (@MonoidAlgebra.of.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
            (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
          (y u v))
      (@DFunLike.coe.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1), max (u_1 + 1) (u_2 + 1), u_3 + 1}
        (@RingHom.{max u_2 u_1, u_3} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) D
          (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
            (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
          (@Semiring.toNonAssocSemiring.{u_3} D (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst_2))))
        (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
        (fun (x : @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) => D)
        (@RingHom.instFunLike.{max u_1 u_2, u_3} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) D
          (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
            (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
          (@Semiring.toNonAssocSemiring.{u_3} D (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst_2))))
        φ))
end

section
universe u_1 u_2 u_3
/-- Theorem 1.4. Original: `NonSofic.linnell`. -/
def theorem_1_4 : Prop :=
  ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r) (K : Type u_1)
  [inst_1 : DivisionRing.{u_1} K]
  [@CharP.{u_1} K
      (@AddGroupWithOne.toAddMonoidWithOne.{u_1} K
        (@Ring.toAddGroupWithOne.{u_1} K (@DivisionRing.toRing.{u_1} K inst_1)))
      q]
  {Λ : Type u_2} [inst_3 : Group.{u_2} Λ]
  (ι :
    @MonoidHom.{0, u_2}
      (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
      Λ
      (@MulOneClass.toMulOne.{0}
        (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
        (@Monoid.toMulOneClass.{0}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          (@DivInvMonoid.toMonoid.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@Group.toDivInvMonoid.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@instGroupPresentedGroup.{0}
                (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
      (@MulOneClass.toMulOne.{u_2} Λ
        (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_3)))))
  (hι :
    @Function.Injective.{1, u_2 + 1}
      (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
        (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
        (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
      Λ
      (@DFunLike.coe.{u_2 + 1, 1, u_2 + 1}
        (@MonoidHom.{0, u_2}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          Λ
          (@MulOneClass.toMulOne.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@Monoid.toMulOneClass.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@DivInvMonoid.toMonoid.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@Group.toDivInvMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@instGroupPresentedGroup.{0}
                    (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
          (@MulOneClass.toMulOne.{u_2} Λ
            (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_3)))))
        (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
          (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
          (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
        (fun
            (x :
              @OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr)) =>
          Λ)
        (@MonoidHom.instFunLike.{0, u_2}
          (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
            (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
            (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
          Λ
          (@MulOneClass.toMulOne.{0}
            (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
              (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
              (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
            (@Monoid.toMulOneClass.{0}
              (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
              (@DivInvMonoid.toMonoid.{0}
                (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                  (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                  (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                (@Group.toDivInvMonoid.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                    (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                  (@instGroupPresentedGroup.{0}
                    (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr))
                    (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r inst d) r
                      (@OAI.Release075.MarkedLineData.presentation q r inst d hr)))))))
          (@MulOneClass.toMulOne.{u_2} Λ
            (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_3)))))
        ι))
  {D : Type u_3} [inst : DivisionRing.{u_3} D]
  (φ :
    @RingHom.{max u_2 u_1, u_3}
      (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K (@DivisionRing.toRing.{u_1} K inst_1))) D
      (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K (@DivisionRing.toRing.{u_1} K inst_1))
        (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_3))))
      (@Semiring.toNonAssocSemiring.{u_3} D (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst)))),
  And (Not (@NonSofic.IsLinnell.{u_1, u_2, u_3} K (@DivisionRing.toRing.{u_1} K inst_1) Λ inst_3 D inst φ))
    (And
      (Not (@NonSofic.IsStronglyHughesFree.{u_1, u_2, u_3} K (@DivisionRing.toRing.{u_1} K inst_1) Λ inst_3 D inst φ))
      (Not (@NonSofic.SatisfiesHF.{u_1, u_2, u_3} K (@DivisionRing.toRing.{u_1} K inst_1) Λ inst_3 D inst φ)))
end

section
universe u_1 u_2 u_3 u_4
/-- Corollary 6.5, algebraic part. Original: `NonSofic.not_isLinnell_of_split`. -/
def corollary_6_5_algebraic : Prop :=
  ∀ {K : Type u_1} [inst : Ring.{u_1} K] {Λ : Type u_2} [inst_1 : Group.{u_2} Λ] {D : Type u_3}
  [inst_2 : DivisionRing.{u_3} D]
  {φ :
    @RingHom.{max u_2 u_1, u_3} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) D
      (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
        (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
      (@Semiring.toNonAssocSemiring.{u_3} D (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst_2)))}
  {I : Type u_4} [inst_3 : Fintype.{u_4} I] {k : Nat}
  (g :
    I →
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Λ)
  (hfree :
    ∀ (i : I),
      @Function.Injective.{1, u_2 + 1} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) Λ
        (@DFunLike.coe.{u_2 + 1, 1, u_2 + 1}
          (@MonoidHom.{0, u_2} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) Λ
            (@MulOneClass.toMulOne.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
              (@Monoid.toMulOneClass.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                (@DivInvMonoid.toMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                  (@Group.toDivInvMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                    (@FreeGroup.instGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))))))
            (@MulOneClass.toMulOne.{u_2} Λ
              (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1)))))
          (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) (fun (x : FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) => Λ)
          (@MonoidHom.instFunLike.{0, u_2} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) Λ
            (@MulOneClass.toMulOne.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
              (@Monoid.toMulOneClass.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                (@DivInvMonoid.toMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                  (@Group.toDivInvMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                    (@FreeGroup.instGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))))))
            (@MulOneClass.toMulOne.{u_2} Λ
              (@Monoid.toMulOneClass.{u_2} Λ (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1)))))
          (@DFunLike.coe.{max (u_2 + 1) 1, max (u_2 + 1) 1, max (u_2 + 1) 1}
            (Equiv.{max 1 (u_2 + 1), max (u_2 + 1) 1} (Prod.{0, 0} (Fin k) (Fin k) → Λ)
              (@MonoidHom.{0, u_2} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) Λ
                (@MulOneClass.toMulOne.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                  (@Monoid.toMulOneClass.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                    (@DivInvMonoid.toMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                      (@Group.toDivInvMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                        (@FreeGroup.instGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))))))
                (@MulOneClass.toMulOne.{u_2} Λ
                  (@Monoid.toMulOneClass.{u_2} Λ
                    (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))
            (Prod.{0, 0} (Fin k) (Fin k) → Λ)
            (fun (x : Prod.{0, 0} (Fin k) (Fin k) → Λ) =>
              @MonoidHom.{0, u_2} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) Λ
                (@MulOneClass.toMulOne.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                  (@Monoid.toMulOneClass.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                    (@DivInvMonoid.toMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                      (@Group.toDivInvMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                        (@FreeGroup.instGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))))))
                (@MulOneClass.toMulOne.{u_2} Λ
                  (@Monoid.toMulOneClass.{u_2} Λ
                    (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1)))))
            (@EquivLike.toFunLike.{max (u_2 + 1) 1, max (u_2 + 1) 1, max (u_2 + 1) 1}
              (Equiv.{max 1 (u_2 + 1), max (u_2 + 1) 1} (Prod.{0, 0} (Fin k) (Fin k) → Λ)
                (@MonoidHom.{0, u_2} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) Λ
                  (@MulOneClass.toMulOne.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                    (@Monoid.toMulOneClass.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                      (@DivInvMonoid.toMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                        (@Group.toDivInvMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                          (@FreeGroup.instGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))))))
                  (@MulOneClass.toMulOne.{u_2} Λ
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))
              (Prod.{0, 0} (Fin k) (Fin k) → Λ)
              (@MonoidHom.{0, u_2} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) Λ
                (@MulOneClass.toMulOne.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                  (@Monoid.toMulOneClass.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                    (@DivInvMonoid.toMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                      (@Group.toDivInvMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                        (@FreeGroup.instGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))))))
                (@MulOneClass.toMulOne.{u_2} Λ
                  (@Monoid.toMulOneClass.{u_2} Λ
                    (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1)))))
              (@Equiv.instEquivLike.{max (u_2 + 1) 1, max (u_2 + 1) 1} (Prod.{0, 0} (Fin k) (Fin k) → Λ)
                (@MonoidHom.{0, u_2} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k))) Λ
                  (@MulOneClass.toMulOne.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                    (@Monoid.toMulOneClass.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                      (@DivInvMonoid.toMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                        (@Group.toDivInvMonoid.{0} (FreeGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))
                          (@FreeGroup.instGroup.{0} (Prod.{0, 0} (Fin k) (Fin k)))))))
                  (@MulOneClass.toMulOne.{u_2} Λ
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1)))))))
            (@FreeGroup.lift.{0, u_2} (Prod.{0, 0} (Fin k) (Fin k)) Λ inst_1) fun (p : Prod.{0, 0} (Fin k) (Fin k)) =>
            @HMul.hMul.{u_2, u_2, u_2} Λ Λ Λ
              (@instHMul.{u_2} Λ
                (@MulOne.toMul.{u_2} Λ
                  (@MulOneClass.toMulOne.{u_2} Λ
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))
              (@HMul.hMul.{u_2, u_2, u_2} Λ Λ Λ
                (@instHMul.{u_2} Λ
                  (@MulOne.toMul.{u_2} Λ
                    (@MulOneClass.toMulOne.{u_2} Λ
                      (@Monoid.toMulOneClass.{u_2} Λ
                        (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))
                (@HMul.hMul.{u_2, u_2, u_2} Λ Λ Λ
                  (@instHMul.{u_2} Λ
                    (@MulOne.toMul.{u_2} Λ
                      (@MulOneClass.toMulOne.{u_2} Λ
                        (@Monoid.toMulOneClass.{u_2} Λ
                          (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))
                  (@Inv.inv.{u_2} Λ
                    (@InvOneClass.toInv.{u_2} Λ
                      (@DivInvOneMonoid.toInvOneClass.{u_2} Λ
                        (@DivisionMonoid.toDivInvOneMonoid.{u_2} Λ (@Group.toDivisionMonoid.{u_2} Λ inst_1))))
                    (g i (@Fin.succ k (@Prod.fst.{0, 0} (Fin k) (Fin k) p))
                      (@OfNat.ofNat.{0}
                        (Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (nat_lit 0)
                        (@Fin.instOfNat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@instNeZeroNatHAdd_1 k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                          (nat_lit 0)))))
                  (g i (@Fin.succ k (@Prod.fst.{0, 0} (Fin k) (Fin k) p))
                    (@Fin.succ k (@Prod.snd.{0, 0} (Fin k) (Fin k) p))))
                (@Inv.inv.{u_2} Λ
                  (@InvOneClass.toInv.{u_2} Λ
                    (@DivInvOneMonoid.toInvOneClass.{u_2} Λ
                      (@DivisionMonoid.toDivInvOneMonoid.{u_2} Λ (@Group.toDivisionMonoid.{u_2} Λ inst_1))))
                  (g i
                    (@OfNat.ofNat.{0}
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (nat_lit 0)
                      (@Fin.instOfNat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@instNeZeroNatHAdd_1 k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                        (nat_lit 0)))
                    (@Fin.succ k (@Prod.snd.{0, 0} (Fin k) (Fin k) p)))))
              (g i
                (@OfNat.ofNat.{0}
                  (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (nat_lit 0)
                  (@Fin.instOfNat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@instNeZeroNatHAdd_1 k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                    (nat_lit 0)))
                (@OfNat.ofNat.{0}
                  (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (nat_lit 0)
                  (@Fin.instOfNat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@instNeZeroNatHAdd_1 k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                    (nat_lit 0)))))))
  (hsum :
    @LT.lt.{0} Real Real.instLT
      (@Finset.sum.{u_4, 0} I Real Real.instAddCommMonoid (@Finset.univ.{u_4} I inst_3) fun (i : I) =>
        @Nat.cast.{0} Real Real.instNatCast
          (@NonSofic.rankD.{u_3, 0, 0} D inst_2
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Matrix.map.{max u_1 u_2, u_3, 0, 0}
              (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) D
              (@DFunLike.coe.{max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1)}
                (Equiv.{max 1 ((max u_1 u_2) + 1), max ((max u_1 u_2) + 1) 1}
                  (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                  (Matrix.{0, 0, max u_1 u_2}
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))))
                (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                (fun
                    (x :
                      Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                        Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) =>
                  Matrix.{0, 0, max u_1 u_2}
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)))
                (@EquivLike.toFunLike.{max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1)}
                  (Equiv.{max 1 ((max u_1 u_2) + 1), max ((max u_1 u_2) + 1) 1}
                    (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                        @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                    (Matrix.{0, 0, max u_1 u_2}
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))))
                  (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                  (Matrix.{0, 0, max u_1 u_2}
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)))
                  (@Equiv.instEquivLike.{max 1 ((max u_1 u_2) + 1), max 1 ((max u_1 u_2) + 1)}
                    (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                        @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                    (Matrix.{0, 0, max u_1 u_2}
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)))))
                (@Matrix.of.{max u_1 u_2, 0, 0}
                  (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)))
                fun
                  (u v :
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                @DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, max (u_1 + 1) (u_2 + 1)}
                  (@MonoidHom.{u_2, max u_2 u_1} Λ (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                    (@MulOneClass.toMulOne.{u_2} Λ
                      (@Monoid.toMulOneClass.{u_2} Λ
                        (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
                    (@MulOneClass.toMulOne.{max u_1 u_2} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                      (@MulZeroOneClass.toMulOneClass.{max u_1 u_2}
                        (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                        (@NonAssocSemiring.toMulZeroOneClass.{max u_1 u_2}
                          (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                          (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
                            (@Monoid.toMulOneClass.{u_2} Λ
                              (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))))
                  Λ (fun (x : Λ) => @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                  (@MonoidHom.instFunLike.{u_2, max u_1 u_2} Λ
                    (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                    (@MulOneClass.toMulOne.{u_2} Λ
                      (@Monoid.toMulOneClass.{u_2} Λ
                        (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
                    (@MulOneClass.toMulOne.{max u_1 u_2} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                      (@MulZeroOneClass.toMulOneClass.{max u_1 u_2}
                        (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                        (@NonAssocSemiring.toMulZeroOneClass.{max u_1 u_2}
                          (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                          (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
                            (@Monoid.toMulOneClass.{u_2} Λ
                              (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))))))
                  (@MonoidAlgebra.of.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
                  (g i u v))
              (@DFunLike.coe.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1), max (u_1 + 1) (u_2 + 1), u_3 + 1}
                (@RingHom.{max u_2 u_1, u_3} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) D
                  (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
                  (@Semiring.toNonAssocSemiring.{u_3} D
                    (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst_2))))
                (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                (fun (x : @MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)) => D)
                (@RingHom.instFunLike.{max u_1 u_2, u_3} (@MonoidAlgebra.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst))
                  D
                  (@MonoidAlgebra.nonAssocSemiring.{u_1, u_2} K Λ (@Ring.toSemiring.{u_1} K inst)
                    (@Monoid.toMulOneClass.{u_2} Λ
                      (@DivInvMonoid.toMonoid.{u_2} Λ (@Group.toDivInvMonoid.{u_2} Λ inst_1))))
                  (@Semiring.toNonAssocSemiring.{u_3} D
                    (@Ring.toSemiring.{u_3} D (@DivisionRing.toRing.{u_3} D inst_2))))
                φ))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_4} I inst_3))
          (@Nat.cast.{0} Real Real.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))),
  Not (@NonSofic.IsLinnell.{u_1, u_2, u_3} K inst Λ inst_1 D inst_2 φ)
end

section
universe u v w
/-- Combined data. Original: `NonSofic.headline_data`. -/
def headline_data : Prop :=
  @Exists.{1} Nat fun (q : Nat) =>
  @Exists.{1} Nat fun (r : Nat) =>
    @Exists.{0} (Nat.Prime q) fun (hq : Nat.Prime q) =>
      have x : Fact (Nat.Prime q) := @Fact.mk (Nat.Prime q) hq;
      @Exists.{2} (@OAI.Release075.MarkedLineData q r x) fun (d : @OAI.Release075.MarkedLineData q r x) =>
        @Exists.{0} (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r)
          fun (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r) =>
          And
            (@Eq.{1} Nat r
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))
            (And (@LT.lt.{0} Nat instLTNat r q)
              (And
                (@OAI.Release075.TorsionFree.{0}
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                    (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                    (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                  (@instGroupPresentedGroup.{0}
                    (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                      (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                    (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                      (@OAI.Release075.MarkedLineData.presentation q r x d hr))))
                (And
                  (@OAI.Release075.WordHyperbolic.{0}
                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                      (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                      (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                    (@instGroupPresentedGroup.{0}
                      (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                        (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                      (@OAI.Release075.BlockPresentation.relators.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                        (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                        (@OAI.Release075.MarkedLineData.presentation q r x d hr))))
                  (And
                    (Not
                      (@Approx252.IsSofic.{0}
                        (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                          (@OAI.Release075.MarkedLineData.Label q r x d)
                          (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                          (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                        (@instGroupPresentedGroup.{0}
                          (@OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                            (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                            (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                          (@OAI.Release075.BlockPresentation.relators.{0, 0}
                            (@OAI.Release075.MarkedLineData.Label q r x d)
                            (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                            (@OAI.Release075.MarkedLineData.presentation q r x d hr)))))
                    (And
                      (∀ (K : Type u) [inst : DivisionRing.{u} K]
                        [@CharP.{u} K
                            (@AddGroupWithOne.toAddMonoidWithOne.{u} K
                              (@Ring.toAddGroupWithOne.{u} K (@DivisionRing.toRing.{u} K inst)))
                            q]
                        (Λ : Type v) [inst_2 : Group.{v} Λ]
                        (ι :
                          @MonoidHom.{0, v}
                            (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                              (@OAI.Release075.MarkedLineData.Label q r x d)
                              (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                              (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                            Λ
                            (@MulOneClass.toMulOne.{0}
                              (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                (@OAI.Release075.MarkedLineData.Label q r x d)
                                (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                              (@Monoid.toMulOneClass.{0}
                                (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                  (@OAI.Release075.MarkedLineData.Label q r x d)
                                  (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                  (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                (@DivInvMonoid.toMonoid.{0}
                                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                    (@OAI.Release075.MarkedLineData.Label q r x d)
                                    (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                    (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                  (@Group.toDivInvMonoid.{0}
                                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                      (@OAI.Release075.MarkedLineData.Label q r x d)
                                      (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                      (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                    (@instGroupPresentedGroup.{0}
                                      (@OAI.Release075.BlockPresentation.Edge.{0, 0}
                                        (@OAI.Release075.MarkedLineData.Label q r x d)
                                        (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                        (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                      (@OAI.Release075.BlockPresentation.relators.{0, 0}
                                        (@OAI.Release075.MarkedLineData.Label q r x d)
                                        (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                        (@OAI.Release075.MarkedLineData.presentation q r x d hr)))))))
                            (@MulOneClass.toMulOne.{v} Λ
                              (@Monoid.toMulOneClass.{v} Λ
                                (@DivInvMonoid.toMonoid.{v} Λ (@Group.toDivInvMonoid.{v} Λ inst_2))))),
                        @Function.Injective.{1, v + 1}
                            (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                              (@OAI.Release075.MarkedLineData.Label q r x d)
                              (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                              (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                            Λ
                            (@DFunLike.coe.{v + 1, 1, v + 1}
                              (@MonoidHom.{0, v}
                                (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                  (@OAI.Release075.MarkedLineData.Label q r x d)
                                  (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                  (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                Λ
                                (@MulOneClass.toMulOne.{0}
                                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                    (@OAI.Release075.MarkedLineData.Label q r x d)
                                    (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                    (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                  (@Monoid.toMulOneClass.{0}
                                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                      (@OAI.Release075.MarkedLineData.Label q r x d)
                                      (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                      (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                    (@DivInvMonoid.toMonoid.{0}
                                      (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                        (@OAI.Release075.MarkedLineData.Label q r x d)
                                        (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                        (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                      (@Group.toDivInvMonoid.{0}
                                        (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                          (@OAI.Release075.MarkedLineData.Label q r x d)
                                          (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                          (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                        (@instGroupPresentedGroup.{0}
                                          (@OAI.Release075.BlockPresentation.Edge.{0, 0}
                                            (@OAI.Release075.MarkedLineData.Label q r x d)
                                            (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                            (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                          (@OAI.Release075.BlockPresentation.relators.{0, 0}
                                            (@OAI.Release075.MarkedLineData.Label q r x d)
                                            (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                            (@OAI.Release075.MarkedLineData.presentation q r x d hr)))))))
                                (@MulOneClass.toMulOne.{v} Λ
                                  (@Monoid.toMulOneClass.{v} Λ
                                    (@DivInvMonoid.toMonoid.{v} Λ (@Group.toDivInvMonoid.{v} Λ inst_2)))))
                              (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                (@OAI.Release075.MarkedLineData.Label q r x d)
                                (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                              (fun
                                  (x :
                                    @OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                      (@OAI.Release075.MarkedLineData.Label q r x d)
                                      (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                      (@OAI.Release075.MarkedLineData.presentation q r x d hr)) =>
                                Λ)
                              (@MonoidHom.instFunLike.{0, v}
                                (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                  (@OAI.Release075.MarkedLineData.Label q r x d)
                                  (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                  (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                Λ
                                (@MulOneClass.toMulOne.{0}
                                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                    (@OAI.Release075.MarkedLineData.Label q r x d)
                                    (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                    (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                  (@Monoid.toMulOneClass.{0}
                                    (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                      (@OAI.Release075.MarkedLineData.Label q r x d)
                                      (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                      (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                    (@DivInvMonoid.toMonoid.{0}
                                      (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                        (@OAI.Release075.MarkedLineData.Label q r x d)
                                        (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                        (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                      (@Group.toDivInvMonoid.{0}
                                        (@OAI.Release075.BlockPresentation.GroupType.{0, 0}
                                          (@OAI.Release075.MarkedLineData.Label q r x d)
                                          (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                          (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                        (@instGroupPresentedGroup.{0}
                                          (@OAI.Release075.BlockPresentation.Edge.{0, 0}
                                            (@OAI.Release075.MarkedLineData.Label q r x d)
                                            (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                            (@OAI.Release075.MarkedLineData.presentation q r x d hr))
                                          (@OAI.Release075.BlockPresentation.relators.{0, 0}
                                            (@OAI.Release075.MarkedLineData.Label q r x d)
                                            (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                                            (@OAI.Release075.MarkedLineData.presentation q r x d hr)))))))
                                (@MulOneClass.toMulOne.{v} Λ
                                  (@Monoid.toMulOneClass.{v} Λ
                                    (@DivInvMonoid.toMonoid.{v} Λ (@Group.toDivInvMonoid.{v} Λ inst_2)))))
                              ι) →
                          ∀ (D : Type w) [inst_3 : DivisionRing.{w} D]
                            (φ :
                              @RingHom.{max v u, w}
                                (@MonoidAlgebra.{u, v} K Λ (@Ring.toSemiring.{u} K (@DivisionRing.toRing.{u} K inst))) D
                                (@MonoidAlgebra.nonAssocSemiring.{u, v} K Λ
                                  (@Ring.toSemiring.{u} K (@DivisionRing.toRing.{u} K inst))
                                  (@Monoid.toMulOneClass.{v} Λ
                                    (@DivInvMonoid.toMonoid.{v} Λ (@Group.toDivInvMonoid.{v} Λ inst_2))))
                                (@Semiring.toNonAssocSemiring.{w} D
                                  (@Ring.toSemiring.{w} D (@DivisionRing.toRing.{w} D inst_3)))),
                            And
                              (Not
                                (@NonSofic.IsLinnell.{u, v, w} K (@DivisionRing.toRing.{u} K inst) Λ inst_2 D inst_3 φ))
                              (And
                                (Not
                                  (@NonSofic.IsStronglyHughesFree.{u, v, w} K (@DivisionRing.toRing.{u} K inst) Λ inst_2
                                    D inst_3 φ))
                                (Not
                                  (@NonSofic.SatisfiesHF.{u, v, w} K (@DivisionRing.toRing.{u} K inst) Λ inst_2 D inst_3
                                    φ))))
                      (∀ (Ω : Type) [inst : Fintype.{0} Ω] [inst_1 : DecidableEq.{1} Ω]
                        (σ :
                          @OAI.Release075.BlockPresentation.Edge.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                              (@OAI.Release075.MarkedLineData.BlockIndex q r x d) r
                              (@OAI.Release075.MarkedLineData.presentation q r x d hr) →
                            Equiv.Perm.{1} Ω)
                        (e k : Nat),
                        @NonSofic.RectFix.{0} q r x d hr Ω inst inst_1 σ e →
                          @LE.le.{0} Nat instLENat
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                e)
                              (@Fintype.card.{0} Ω inst) →
                            @LT.lt.{0} Nat instLTNat
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) r)
                                    q)
                                  k)
                                (@Fintype.card.{0} Ω inst) →
                              @Exists.{1} (@OAI.Release075.MarkedLineData.BlockIndex q r x d)
                                fun (b : @OAI.Release075.MarkedLineData.BlockIndex q r x d) =>
                                @Exists.{1}
                                  (@Subtype.{1} (@OAI.Release075.MarkedLineData.Label q r x d)
                                    fun (x_1 : @OAI.Release075.MarkedLineData.Label q r x d) =>
                                    @Membership.mem.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                                      (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r x d))
                                      (@SetLike.instMembership.{0, 0}
                                        (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r x d))
                                        (@OAI.Release075.MarkedLineData.Label q r x d)
                                        (@Finset.instSetLike.{0} (@OAI.Release075.MarkedLineData.Label q r x d)))
                                      (@OAI.Release075.CartesianBlock.labels.{0}
                                        (@OAI.Release075.MarkedLineData.Label q r x d) r
                                        (@OAI.Release075.MarkedLineData.block q r x d hr b))
                                      x_1)
                                  fun
                                    (i :
                                      @Subtype.{1} (@OAI.Release075.MarkedLineData.Label q r x d)
                                        fun (x_1 : @OAI.Release075.MarkedLineData.Label q r x d) =>
                                        @Membership.mem.{0, 0} (@OAI.Release075.MarkedLineData.Label q r x d)
                                          (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r x d))
                                          (@SetLike.instMembership.{0, 0}
                                            (Finset.{0} (@OAI.Release075.MarkedLineData.Label q r x d))
                                            (@OAI.Release075.MarkedLineData.Label q r x d)
                                            (@Finset.instSetLike.{0} (@OAI.Release075.MarkedLineData.Label q r x d)))
                                          (@OAI.Release075.CartesianBlock.labels.{0}
                                            (@OAI.Release075.MarkedLineData.Label q r x d) r
                                            (@OAI.Release075.MarkedLineData.block q r x d hr b))
                                          x_1) =>
                                  @Exists.{1} (Fin r) fun (u : Fin r) =>
                                    @Exists.{1} (Fin r) fun (v : Fin r) =>
                                      @LT.lt.{0} Nat instLTNat k
                                        (@NonSofic.triangleSupport.{0} q r x d hr Ω inst inst_1 σ b i u v)))))))
end

section
universe u v w
/-- Combined statement. Original: `NonSofic.headline`. -/
def headline : Prop :=
  @Exists.{1} Nat fun (q : Nat) =>
  @Exists.{0} (Nat.Prime q) fun (x : Nat.Prime q) =>
    @Exists.{2} Type fun (G : Type) =>
      @Exists.{1} (Group.{0} G) fun (x : Group.{0} G) =>
        And (@OAI.Release075.TorsionFree.{0} G x)
          (And (@OAI.Release075.WordHyperbolic.{0} G x)
            (And (Not (@Approx252.IsSofic.{0} G x))
              (∀ (K : Type u) [inst : DivisionRing.{u} K]
                [@CharP.{u} K
                    (@AddGroupWithOne.toAddMonoidWithOne.{u} K
                      (@Ring.toAddGroupWithOne.{u} K (@DivisionRing.toRing.{u} K inst)))
                    q]
                (Λ : Type v) [inst_2 : Group.{v} Λ]
                (ι :
                  @MonoidHom.{0, v} G Λ
                    (@MulOneClass.toMulOne.{0} G
                      (@Monoid.toMulOneClass.{0} G (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G x))))
                    (@MulOneClass.toMulOne.{v} Λ
                      (@Monoid.toMulOneClass.{v} Λ
                        (@DivInvMonoid.toMonoid.{v} Λ (@Group.toDivInvMonoid.{v} Λ inst_2))))),
                @Function.Injective.{1, v + 1} G Λ
                    (@DFunLike.coe.{v + 1, 1, v + 1}
                      (@MonoidHom.{0, v} G Λ
                        (@MulOneClass.toMulOne.{0} G
                          (@Monoid.toMulOneClass.{0} G (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G x))))
                        (@MulOneClass.toMulOne.{v} Λ
                          (@Monoid.toMulOneClass.{v} Λ
                            (@DivInvMonoid.toMonoid.{v} Λ (@Group.toDivInvMonoid.{v} Λ inst_2)))))
                      G (fun (x : G) => Λ)
                      (@MonoidHom.instFunLike.{0, v} G Λ
                        (@MulOneClass.toMulOne.{0} G
                          (@Monoid.toMulOneClass.{0} G (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G x))))
                        (@MulOneClass.toMulOne.{v} Λ
                          (@Monoid.toMulOneClass.{v} Λ
                            (@DivInvMonoid.toMonoid.{v} Λ (@Group.toDivInvMonoid.{v} Λ inst_2)))))
                      ι) →
                  ∀ (D : Type w) [inst_3 : DivisionRing.{w} D]
                    (φ :
                      @RingHom.{max v u, w}
                        (@MonoidAlgebra.{u, v} K Λ (@Ring.toSemiring.{u} K (@DivisionRing.toRing.{u} K inst))) D
                        (@MonoidAlgebra.nonAssocSemiring.{u, v} K Λ
                          (@Ring.toSemiring.{u} K (@DivisionRing.toRing.{u} K inst))
                          (@Monoid.toMulOneClass.{v} Λ
                            (@DivInvMonoid.toMonoid.{v} Λ (@Group.toDivInvMonoid.{v} Λ inst_2))))
                        (@Semiring.toNonAssocSemiring.{w} D
                          (@Ring.toSemiring.{w} D (@DivisionRing.toRing.{w} D inst_3)))),
                    And (Not (@NonSofic.IsLinnell.{u, v, w} K (@DivisionRing.toRing.{u} K inst) Λ inst_2 D inst_3 φ))
                      (And
                        (Not
                          (@NonSofic.IsStronglyHughesFree.{u, v, w} K (@DivisionRing.toRing.{u} K inst) Λ inst_2 D
                            inst_3 φ))
                        (Not
                          (@NonSofic.SatisfiesHF.{u, v, w} K (@DivisionRing.toRing.{u} K inst) Λ inst_2 D inst_3 φ))))))
end

end PaperStatements
