import Proofs
set_option maxRecDepth 100000

/-! Frozen exact-type checks and axiom audit of every headline. -/

-- Theorem 1.1 (v1.0)
#check (@Approx252.exists_torsionFree_wordHyperbolic_not_sofic : PaperStatements.theorem_1_1)
#print axioms Approx252.exists_torsionFree_wordHyperbolic_not_sofic
#print axioms PaperProofs.theorem_1_1

-- Theorem 3.1 (thm:ineq)
#check (@NonSofic.presentation_ineq : PaperStatements.theorem_3_1)
#print axioms NonSofic.presentation_ineq
#print axioms PaperProofs.theorem_3_1

-- Theorem 1.2, general constant
#check (@NonSofic.presentation_quant : PaperStatements.theorem_1_2_general)
#print axioms NonSofic.presentation_quant
#print axioms PaperProofs.theorem_1_2_general

-- Theorem 1.2, Lemma 2.2 data
#check (@NonSofic.quant_lemma22 : PaperStatements.theorem_1_2_lemma22)
#print axioms NonSofic.quant_lemma22
#print axioms PaperProofs.theorem_1_2_lemma22

-- Corollary 1.3, universal word
#check (@NonSofic.exists_rect_word_killed_by_sofic_univ : PaperStatements.corollary_1_3_word)
#print axioms NonSofic.exists_rect_word_killed_by_sofic_univ
#print axioms PaperProofs.corollary_1_3_word

-- Corollary 1.3, quotient
#check (@NonSofic.quotient_not_sofic : PaperStatements.corollary_1_3_quotient)
#print axioms NonSofic.quotient_not_sofic
#print axioms PaperProofs.corollary_1_3_quotient

-- Lemma 6.2
#check (@NonSofic.LineFree.lineSubgroup_free : PaperStatements.lemma_6_2)
#print axioms NonSofic.LineFree.lineSubgroup_free
#print axioms PaperProofs.lemma_6_2

-- Theorem 6.1
#check (@NonSofic.collapse : PaperStatements.theorem_6_1)
#print axioms NonSofic.collapse
#print axioms PaperProofs.theorem_6_1

-- Theorem 6.1, group ring
#check (@NonSofic.collapse_groupRing : PaperStatements.theorem_6_1_groupRing)
#print axioms NonSofic.collapse_groupRing
#print axioms PaperProofs.theorem_6_1_groupRing

-- Lemma 6.3
#check (@NonSofic.isUnit_map_of_zQuotientData : PaperStatements.lemma_6_3)
#print axioms NonSofic.isUnit_map_of_zQuotientData
#print axioms PaperProofs.lemma_6_3

-- Theorem 1.4
#check (@NonSofic.linnell : PaperStatements.theorem_1_4)
#print axioms NonSofic.linnell
#print axioms PaperProofs.theorem_1_4

-- Corollary 6.5, algebraic part
#check (@NonSofic.not_isLinnell_of_split : PaperStatements.corollary_6_5_algebraic)
#print axioms NonSofic.not_isLinnell_of_split
#print axioms PaperProofs.corollary_6_5_algebraic

-- Combined data
#check (@NonSofic.headline_data : PaperStatements.headline_data)
#print axioms NonSofic.headline_data
#print axioms PaperProofs.headline_data

-- Combined statement
#check (@NonSofic.headline : PaperStatements.headline)
#print axioms NonSofic.headline
#print axioms PaperProofs.headline

-- Additional original audit root: NonSofic.IsSofic.subgroup
section
universe u_1
example : ∀ {G : Type u_1} [inst : Group.{u_1} G] (hG : @Approx252.IsSofic.{u_1} G inst) (K : @Subgroup.{u_1} G inst),
  @Approx252.IsSofic.{u_1}
    (@Subtype.{u_1 + 1} G fun (x : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
    (@Subgroup.toGroup.{u_1} G inst K) := @NonSofic.IsSofic.subgroup.{u_1}
end
#print axioms NonSofic.IsSofic.subgroup

-- Additional original audit root: NonSofic.isSofic_pi
section
universe u_1 u_2
example : ∀ {J : Type u_1} [Fintype.{u_1} J] [DecidableEq.{u_1 + 1} J] {H : J → Type u_2} [inst : (j : J) → Group.{u_2} (H j)]
  (hH : ∀ (j : J), @Approx252.IsSofic.{u_2} (H j) (inst j)),
  @Approx252.IsSofic.{max u_1 u_2} ((j : J) → H j) (@Pi.group.{u_1, u_2} J H inst) := @NonSofic.isSofic_pi.{u_1, u_2}
end
#print axioms NonSofic.isSofic_pi

-- Additional original audit root: NonSofic.exists_rect_word_killed_by_sofic
section
universe u
example : ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r)
  (hq : @LT.lt.{0} Nat instLTNat r q),
  @Exists.{1} (@NonSofic.RectIndex q r inst d) fun (x : @NonSofic.RectIndex q r inst d) =>
    And
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
                  (@OAI.Release075.BlockPresentation.GroupType.{0, 0} (@OAI.Release075.MarkedLineData.Label q r inst d)
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
                    (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst_1)))))
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
                    (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst_1)))))
                π (@NonSofic.rectWord q r inst d hr x))
              (@OfNat.ofNat.{u} H (nat_lit 1)
                (@One.toOfNat1.{u} H
                  (@InvOneClass.toOne.{u} H
                    (@DivInvOneMonoid.toInvOneClass.{u} H
                      (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst_1))))))) := @NonSofic.exists_rect_word_killed_by_sofic.{u}
end
#print axioms NonSofic.exists_rect_word_killed_by_sofic

-- Additional original audit root: NonSofic.two_hundred_le
section
example : ∀ {q r : Nat} [inst : Fact (Nat.Prime q)] (d : @OAI.Release075.MarkedLineData q r inst),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) q := @NonSofic.two_hundred_le
end
#print axioms NonSofic.two_hundred_le

-- Additional original audit root: NonSofic.unit_isLinnell
section
universe u_1
example : ∀ (K : Type u_1) [inst : DivisionRing.{u_1} K],
  @NonSofic.IsLinnell.{u_1, 0, u_1} K (@DivisionRing.toRing.{u_1} K inst) Unit
    (@CommGroup.toGroup.{0} Unit PUnit.commGroup.{0}) K inst (@NonSofic.unitHom.{u_1} K inst) := @NonSofic.unit_isLinnell.{u_1}
end
#print axioms NonSofic.unit_isLinnell

-- Additional original audit root: NonSofic.int_hf_premises
section
example : And
  (@NonSofic.IsFinitelyGenerated.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup)
    (@Top.top.{0} (@Subgroup.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup))
      (@Subgroup.instTop.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup))))
  (And
    (@NonSofic.IsNormalIn.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup)
      (@Bot.bot.{0} (@Subgroup.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup))
        (@Subgroup.instBot.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup)))
      (@Top.top.{0} (@Subgroup.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup))
        (@Subgroup.instTop.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup))))
    (@NonSofic.IsInfCyclicQuotient.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup)
      (@Bot.bot.{0} (@Subgroup.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup))
        (@Subgroup.instBot.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup)))
      (@Top.top.{0} (@Subgroup.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup))
        (@Subgroup.instTop.{0} (Multiplicative.{0} Int) (@Multiplicative.group.{0} Int Int.instAddGroup)))
      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} Int (Multiplicative.{0} Int)) Int (fun (x : Int) => Multiplicative.{0} Int)
        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} Int (Multiplicative.{0} Int)) Int (Multiplicative.{0} Int)
          (@Equiv.instEquivLike.{1, 1} Int (Multiplicative.{0} Int)))
        (@Multiplicative.ofAdd.{0} Int) (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := @NonSofic.int_hf_premises
end
#print axioms NonSofic.int_hf_premises
