/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import CompPoly.Fields.Binary.BF128Ghash.Prelude


-- @@ L10-14 verbatim
/-!
# XPowTwoPow Mod Certificate

Certificates for modular arithmetic in the BF128Ghash field.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace BF128Ghash

-- @@ L19-19 verbatim
open Polynomial


-- @@ L21-21 verbatim
set_option maxRecDepth 1500


-- @@ L23-23 verbatim
def r0Val : B128 := X_val

-- @@ L24-24 verbatim
noncomputable def r0 := X_ZMod2Poly

-- @@ L25-25 verbatim
def q1Val : B128 := BitVec.ofNat 128 0

-- @@ L26-26 verbatim
def r1Val : B128 := BitVec.ofNat 128 4

-- @@ L27-30 verbatim
noncomputable def r1 := toPoly r1Val
lemma step_1 : r0^2 = (toPoly (to256 q1Val)) * ghashPoly + r1 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r0Val q1Val r1Val; rfl -- Kernel check


-- @@ L32-32 verbatim
def q2Val : B128 := BitVec.ofNat 128 0

-- @@ L33-33 verbatim
def r2Val : B128 := BitVec.ofNat 128 16

-- @@ L34-37 verbatim
noncomputable def r2 := toPoly r2Val
lemma step_2 : r1^2 = (toPoly (to256 q2Val)) * ghashPoly + r2 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r1Val q2Val r2Val; rfl -- Kernel check


-- @@ L39-39 verbatim
def q3Val : B128 := BitVec.ofNat 128 0

-- @@ L40-40 verbatim
def r3Val : B128 := BitVec.ofNat 128 256

-- @@ L41-44 verbatim
noncomputable def r3 := toPoly r3Val
lemma step_3 : r2^2 = (toPoly (to256 q3Val)) * ghashPoly + r3 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r2Val q3Val r3Val; rfl -- Kernel check


-- @@ L46-46 verbatim
def q4Val : B128 := BitVec.ofNat 128 0

-- @@ L47-47 verbatim
def r4Val : B128 := BitVec.ofNat 128 65536

-- @@ L48-51 verbatim
noncomputable def r4 := toPoly r4Val
lemma step_4 : r3^2 = (toPoly (to256 q4Val)) * ghashPoly + r4 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r3Val q4Val r4Val; rfl -- Kernel check


-- @@ L53-53 verbatim
def q5Val : B128 := BitVec.ofNat 128 0

-- @@ L54-54 verbatim
def r5Val : B128 := BitVec.ofNat 128 4294967296

-- @@ L55-58 verbatim
noncomputable def r5 := toPoly r5Val
lemma step_5 : r4^2 = (toPoly (to256 q5Val)) * ghashPoly + r5 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r4Val q5Val r5Val; rfl -- Kernel check


-- @@ L60-60 verbatim
def q6Val : B128 := BitVec.ofNat 128 0

-- @@ L61-61 verbatim
def r6Val : B128 := BitVec.ofNat 128 18446744073709551616

-- @@ L62-65 verbatim
noncomputable def r6 := toPoly r6Val
lemma step_6 : r5^2 = (toPoly (to256 q6Val)) * ghashPoly + r6 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r5Val q6Val r6Val; rfl -- Kernel check


-- @@ L67-67 verbatim
def q7Val : B128 := BitVec.ofNat 128 1

-- @@ L68-68 verbatim
def r7Val : B128 := BitVec.ofNat 128 135

-- @@ L69-72 verbatim
noncomputable def r7 := toPoly r7Val
lemma step_7 : r6^2 = (toPoly (to256 q7Val)) * ghashPoly + r7 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r6Val q7Val r7Val; rfl -- Kernel check


-- @@ L74-74 verbatim
def q8Val : B128 := BitVec.ofNat 128 0

-- @@ L75-75 verbatim
def r8Val : B128 := BitVec.ofNat 128 16405

-- @@ L76-79 verbatim
noncomputable def r8 := toPoly r8Val
lemma step_8 : r7^2 = (toPoly (to256 q8Val)) * ghashPoly + r8 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r7Val q8Val r8Val; rfl -- Kernel check


-- @@ L81-81 verbatim
def q9Val : B128 := BitVec.ofNat 128 0

-- @@ L82-82 verbatim
def r9Val : B128 := BitVec.ofNat 128 268435729

-- @@ L83-86 verbatim
noncomputable def r9 := toPoly r9Val
lemma step_9 : r8^2 = (toPoly (to256 q9Val)) * ghashPoly + r9 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r8Val q9Val r9Val; rfl -- Kernel check


-- @@ L88-88 verbatim
def q10Val : B128 := BitVec.ofNat 128 0

-- @@ L89-89 verbatim
def r10Val : B128 := BitVec.ofNat 128 72057594037993729

-- @@ L90-93 verbatim
noncomputable def r10 := toPoly r10Val
lemma step_10 : r9^2 = (toPoly (to256 q10Val)) * ghashPoly + r10 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r9Val q10Val r10Val; rfl -- Kernel check


-- @@ L95-95 verbatim
def q11Val : B128 := BitVec.ofNat 128 0

-- @@ L96-96 verbatim
def r11Val : B128 := BitVec.ofNat 128 5192296858534827628530500624252929

-- @@ L97-100 verbatim
noncomputable def r11 := toPoly r11Val
lemma step_11 : r10^2 = (toPoly (to256 q11Val)) * ghashPoly + r11 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r10Val q11Val r11Val; rfl -- Kernel check


-- @@ L102-102 verbatim
def q12Val : B128 := BitVec.ofNat 128 79228162514264337593543950336

-- @@ L103-103 verbatim
def r12Val : B128 := BitVec.ofNat 128 10695801939444132319206437814273

-- @@ L104-107 verbatim
noncomputable def r12 := toPoly r12Val
lemma step_12 : r11^2 = (toPoly (to256 q12Val)) * ghashPoly + r12 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r11Val q12Val r12Val; rfl -- Kernel check


-- @@ L109-109 verbatim
def q13Val : B128 := BitVec.ofNat 128 302618836529205194260481

-- @@ L110-110 verbatim
def r13Val : B128 := BitVec.ofNat 128 40852786614935679133548678

-- @@ L111-114 verbatim
noncomputable def r13 := toPoly r13Val
lemma step_13 : r12^2 = (toPoly (to256 q13Val)) * ghashPoly + r13 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r12Val q13Val r13Val; rfl -- Kernel check


-- @@ L116-116 verbatim
def q14Val : B128 := BitVec.ofNat 128 4403688133700

-- @@ L117-117 verbatim
def r14Val : B128 := BitVec.ofNat 128 594486085799880

-- @@ L118-121 verbatim
noncomputable def r14 := toPoly r14Val
lemma step_14 : r13^2 = (toPoly (to256 q14Val)) * ghashPoly + r14 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r13Val q14Val r14Val; rfl -- Kernel check


-- @@ L123-123 verbatim
def q15Val : B128 := BitVec.ofNat 128 0

-- @@ L124-124 verbatim
def r15Val : B128 := BitVec.ofNat 128 317319171807580447641733255232

-- @@ L125-128 verbatim
noncomputable def r15 := toPoly r15Val
lemma step_15 : r14^2 = (toPoly (to256 q15Val)) * ghashPoly + r15 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r14Val q15Val r15Val; rfl -- Kernel check


-- @@ L130-130 verbatim
def q16Val : B128 := BitVec.ofNat 128 295148205346296697104

-- @@ L131-131 verbatim
def r16Val : B128 := BitVec.ofNat 128 21272841581577792734377501409119104880

-- @@ L132-135 verbatim
noncomputable def r16 := toPoly r16Val
lemma step_16 : r15^2 = (toPoly (to256 q16Val)) * ghashPoly + r16 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r15Val q16Val r16Val; rfl -- Kernel check


-- @@ L137-137 verbatim
def q17Val : B128 := BitVec.ofNat 128 1329228075013083128053711770004558849

-- @@ L138-138 verbatim
def r17Val : B128 := BitVec.ofNat 128 178123058470187579300754373079857658247

-- @@ L139-142 verbatim
noncomputable def r17 := toPoly r17Val
lemma step_17 : r16^2 = (toPoly (to256 q17Val)) * ghashPoly + r17 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r16Val q17Val r17Val; rfl -- Kernel check


-- @@ L144-144 verbatim
def q18Val : B128 := BitVec.ofNat 128 85174437751585617676521693081345740853

-- @@ L145-145 verbatim
def r18Val : B128 := BitVec.ofNat 128 185309517472602589216710143146226674206

-- @@ L146-149 verbatim
noncomputable def r18 := toPoly r18Val
lemma step_18 : r17^2 = (toPoly (to256 q18Val)) * ghashPoly + r18 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r17Val q18Val r18Val; rfl -- Kernel check


-- @@ L151-151 verbatim
def q19Val : B128 := BitVec.ofNat 128 85429271016757708826772846602701832224

-- @@ L152-152 verbatim
def r19Val : B128 := BitVec.ofNat 128 243359572833697916948025442825716044212

-- @@ L153-156 verbatim
noncomputable def r19 := toPoly r19Val
lemma step_19 : r18^2 = (toPoly (to256 q19Val)) * ghashPoly + r19 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r18Val q19Val r19Val; rfl -- Kernel check


-- @@ L158-158 verbatim
def q20Val : B128 := BitVec.ofNat 128 91825791577816695462331943916582015331

-- @@ L159-159 verbatim
def r20Val : B128 := BitVec.ofNat 128 2242402909557391341593841539292758713

-- @@ L160-163 verbatim
noncomputable def r20 := toPoly r20Val
lemma step_20 : r19^2 = (toPoly (to256 q20Val)) * ghashPoly + r20 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r19Val q20Val r20Val; rfl -- Kernel check


-- @@ L165-165 verbatim
def q21Val : B128 := BitVec.ofNat 128 6578260275635393025015507911528788

-- @@ L166-166 verbatim
def r21Val : B128 := BitVec.ofNat 128 23534795660742517158384838884479883757

-- @@ L167-170 verbatim
noncomputable def r21 := toPoly r21Val
lemma step_21 : r20^2 = (toPoly (to256 q21Val)) * ghashPoly + r21 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r20Val q21Val r21Val; rfl -- Kernel check


-- @@ L172-172 verbatim
def q22Val : B128 := BitVec.ofNat 128 1335821067607728284447314588529135620

-- @@ L173-173 verbatim
def r22Val : B128 := BitVec.ofNat 128 174985988737277424980776175160916846157

-- @@ L174-177 verbatim
noncomputable def r22 := toPoly r22Val
lemma step_22 : r21^2 = (toPoly (to256 q22Val)) * ghashPoly + r22 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r21Val q22Val r22Val; rfl -- Kernel check


-- @@ L179-179 verbatim
def q23Val : B128 := BitVec.ofNat 128 85097933765574711371307601252685529380

-- @@ L180-180 verbatim
def r23Val : B128 := BitVec.ofNat 128 175030095290142335996286672108454299053

-- @@ L181-184 verbatim
noncomputable def r23 := toPoly r23Val
lemma step_23 : r22^2 = (toPoly (to256 q23Val)) * ghashPoly + r23 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r22Val q23Val r23Val; rfl -- Kernel check


-- @@ L186-186 verbatim
def q24Val : B128 := BitVec.ofNat 128 85097938855979638311968046394211651956

-- @@ L187-187 verbatim
def r24Val : B128 := BitVec.ofNat 128 265807388946362947165055761130818848797

-- @@ L188-191 verbatim
noncomputable def r24 := toPoly r24Val
lemma step_24 : r23^2 = (toPoly (to256 q24Val)) * ghashPoly + r24 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r23Val q24Val r24Val; rfl -- Kernel check


-- @@ L193-193 verbatim
def q25Val : B128 := BitVec.ofNat 128 106449006993305541109351437619337171064

-- @@ L194-194 verbatim
def r25Val : B128 := BitVec.ofNat 128 249252559114209554249604311851685858361

-- @@ L195-198 verbatim
noncomputable def r25 := toPoly r25Val
lemma step_25 : r24^2 = (toPoly (to256 q25Val)) * ghashPoly + r25 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r24Val q25Val r25Val; rfl -- Kernel check


-- @@ L200-200 verbatim
def q26Val : B128 := BitVec.ofNat 128 92076299539298910085337233284453712951

-- @@ L201-201 verbatim
def r26Val : B128 := BitVec.ofNat 128 58796763164556581763983006251523293764

-- @@ L202-205 verbatim
noncomputable def r26 := toPoly r26Val
lemma step_26 : r25^2 = (toPoly (to256 q26Val)) * ghashPoly + r26 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r25Val q26Val r26Val; rfl -- Kernel check


-- @@ L207-207 verbatim
def q27Val : B128 := BitVec.ofNat 128 5732402635759363598497704284982935635

-- @@ L208-208 verbatim
def r27Val : B128 := BitVec.ofNat 128 49134626841591323031921206452464859177

-- @@ L209-212 verbatim
noncomputable def r27 := toPoly r27Val
lemma step_27 : r26^2 = (toPoly (to256 q27Val)) * ghashPoly + r27 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r26Val q27Val r27Val; rfl -- Kernel check


-- @@ L214-214 verbatim
def q28Val : B128 := BitVec.ofNat 128 5401714348658740294254131118417904902

-- @@ L215-215 verbatim
def r28Val : B128 := BitVec.ofNat 128 27987540068191889485421864406071811155

-- @@ L216-219 verbatim
noncomputable def r28 := toPoly r28Val
lemma step_28 : r27^2 = (toPoly (to256 q28Val)) * ghashPoly + r28 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r27Val q28Val r28Val; rfl -- Kernel check


-- @@ L221-221 verbatim
def q29Val : B128 := BitVec.ofNat 128 1417503699112502653188969622685433860

-- @@ L222-222 verbatim
def r29Val : B128 := BitVec.ofNat 128 271029757364165806137532465049589437209

-- @@ L223-226 verbatim
noncomputable def r29 := toPoly r29Val
lemma step_29 : r28^2 = (toPoly (to256 q29Val)) * ghashPoly + r29 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r28Val q29Val r29Val; rfl -- Kernel check


-- @@ L228-228 verbatim
def q30Val : B128 := BitVec.ofNat 128 106698213459293707051433245069331939437

-- @@ L229-229 verbatim
def r30Val : B128 := BitVec.ofNat 128 280724925951004403811542151209009346242

-- @@ L230-233 verbatim
noncomputable def r30 := toPoly r30Val
lemma step_30 : r29^2 = (toPoly (to256 q30Val)) * ghashPoly + r30 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r29Val q30Val r30Val; rfl -- Kernel check


-- @@ L235-235 verbatim
def q31Val : B128 := BitVec.ofNat 128 107693530655217507989114849941793018940

-- @@ L236-236 verbatim
def r31Val : B128 := BitVec.ofNat 128 128752713728467045721822022561693573808

-- @@ L237-240 verbatim
noncomputable def r31 := toPoly r31Val
lemma step_31 : r30^2 = (toPoly (to256 q31Val)) * ghashPoly + r31 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r30Val q31Val r31Val; rfl -- Kernel check


-- @@ L242-242 verbatim
def q32Val : B128 := BitVec.ofNat 128 26586209154299446928674418544604102926

-- @@ L243-243 verbatim
def r32Val : B128 := BitVec.ofNat 128 159741227827866894033846763158209103146

-- @@ L244-247 verbatim
noncomputable def r32 := toPoly r32Val
lemma step_32 : r31^2 = (toPoly (to256 q32Val)) * ghashPoly + r32 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r31Val q32Val r32Val; rfl -- Kernel check


-- @@ L249-249 verbatim
def q33Val : B128 := BitVec.ofNat 128 28246182457631555671140354653794861386

-- @@ L250-250 verbatim
def r33Val : B128 := BitVec.ofNat 128 274834116766907886484561602157405644722

-- @@ L251-254 verbatim
noncomputable def r33 := toPoly r33Val
lemma step_33 : r32^2 = (toPoly (to256 q33Val)) * ghashPoly + r33 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r32Val q33Val r33Val; rfl -- Kernel check


-- @@ L256-256 verbatim
def q34Val : B128 := BitVec.ofNat 128 106776015589057259060961011925506130044

-- @@ L257-257 verbatim
def r34Val : B128 := BitVec.ofNat 128 269592872973127703478481607229849893488

-- @@ L258-261 verbatim
noncomputable def r34 := toPoly r34Val
lemma step_34 : r33^2 = (toPoly (to256 q34Val)) * ghashPoly + r34 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r33Val q34Val r34Val; rfl -- Kernel check


-- @@ L263-263 verbatim
def q35Val : B128 := BitVec.ofNat 128 106692958824939381797454263554624721276

-- @@ L264-264 verbatim
def r35Val : B128 := BitVec.ofNat 128 281740353144251213267627901976484830580

-- @@ L265-268 verbatim
noncomputable def r35 := toPoly r35Val
lemma step_35 : r34^2 = (toPoly (to256 q35Val)) * ghashPoly + r35 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r34Val q35Val r35Val; rfl -- Kernel check


-- @@ L270-270 verbatim
def q36Val : B128 := BitVec.ofNat 128 107695154496139142149109455169944552508

-- @@ L271-271 verbatim
def r36Val : B128 := BitVec.ofNat 128 43449847600466687806806694967245739940

-- @@ L272-275 verbatim
noncomputable def r36 := toPoly r36Val
lemma step_36 : r35^2 = (toPoly (to256 q36Val)) * ghashPoly + r36 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r35Val q36Val r36Val; rfl -- Kernel check


-- @@ L277-277 verbatim
def q37Val : B128 := BitVec.ofNat 128 5318311470645487902434602580876197954

-- @@ L278-278 verbatim
def r37Val : B128 := BitVec.ofNat 128 37727843099595198433684011782007776478

-- @@ L279-282 verbatim
noncomputable def r37 := toPoly r37Val
lemma step_37 : r36^2 = (toPoly (to256 q37Val)) * ghashPoly + r37 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r36Val q37Val r37Val; rfl -- Kernel check


-- @@ L284-284 verbatim
def q38Val : B128 := BitVec.ofNat 128 1745017709983535898810543976869807188

-- @@ L285-285 verbatim
def r38Val : B128 := BitVec.ofNat 128 311928417185453978908537250809886516984

-- @@ L286-289 verbatim
noncomputable def r38 := toPoly r38Val
lemma step_38 : r37^2 = (toPoly (to256 q38Val)) * ghashPoly + r38 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r37Val q38Val r38Val; rfl -- Kernel check


-- @@ L291-291 verbatim
def q39Val : B128 := BitVec.ofNat 128 112009612504539276871140401964429693999

-- @@ L292-292 verbatim
def r39Val : B128 := BitVec.ofNat 128 297740222968517774644413722072226000397

-- @@ L293-296 verbatim
noncomputable def r39 := toPoly r39Val
lemma step_39 : r38^2 = (toPoly (to256 q39Val)) * ghashPoly + r39 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r38Val q39Val r39Val; rfl -- Kernel check


-- @@ L298-298 verbatim
def q40Val : B128 := BitVec.ofNat 128 108110543572682219842640169583646098477

-- @@ L299-299 verbatim
def r40Val : B128 := BitVec.ofNat 128 32339339626698503367513300576590613010

-- @@ L300-303 verbatim
noncomputable def r40 := toPoly r40Val
lemma step_40 : r39^2 = (toPoly (to256 q40Val)) * ghashPoly + r40 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r39Val q40Val r40Val; rfl -- Kernel check


-- @@ L305-305 verbatim
def q41Val : B128 := BitVec.ofNat 128 1661881068625898637091009420418367572

-- @@ L306-306 verbatim
def r41Val : B128 := BitVec.ofNat 128 223132434853550809815195064548738067112

-- @@ L307-310 verbatim
noncomputable def r41 := toPoly r41Val
lemma step_41 : r40^2 = (toPoly (to256 q41Val)) * ghashPoly + r41 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r40Val q41Val r41Val; rfl -- Kernel check


-- @@ L312-312 verbatim
def q42Val : B128 := BitVec.ofNat 128 90498191261518681257739264897661080691

-- @@ L313-313 verbatim
def r42Val : B128 := BitVec.ofNat 128 265523960741914972480486897956328640665

-- @@ L314-317 verbatim
noncomputable def r42 := toPoly r42Val
lemma step_42 : r41^2 = (toPoly (to256 q42Val)) * ghashPoly + r42 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r41Val q42Val r42Val; rfl -- Kernel check


-- @@ L319-319 verbatim
def q43Val : B128 := BitVec.ofNat 128 106448900806604993173560670687746606380

-- @@ L320-320 verbatim
def r43Val : B128 := BitVec.ofNat 128 317476001073086156486538380654899563653

-- @@ L321-324 verbatim
noncomputable def r43 := toPoly r43Val
lemma step_43 : r42^2 = (toPoly (to256 q43Val)) * ghashPoly + r43 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r42Val q43Val r43Val; rfl -- Kernel check


-- @@ L326-326 verbatim
def q44Val : B128 := BitVec.ofNat 128 112092949142089617020436155326729814143

-- @@ L327-327 verbatim
def r44Val : B128 := BitVec.ofNat 128 281134273668648985900959546328737677036

-- @@ L328-331 verbatim
noncomputable def r44 := toPoly r44Val
lemma step_44 : r43^2 = (toPoly (to256 q44Val)) * ghashPoly + r44 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r43Val q44Val r44Val; rfl -- Kernel check


-- @@ L333-333 verbatim
def q45Val : B128 := BitVec.ofNat 128 107694727223682985464461035033154818152

-- @@ L334-334 verbatim
def r45Val : B128 := BitVec.ofNat 128 134228771238834113055021444037992255816

-- @@ L335-338 verbatim
noncomputable def r45 := toPoly r45Val
lemma step_45 : r44^2 = (toPoly (to256 q45Val)) * ghashPoly + r45 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r44Val q45Val r45Val; rfl -- Kernel check


-- @@ L340-340 verbatim
def q46Val : B128 := BitVec.ofNat 128 26669366156822072797831484246999700558

-- @@ L341-341 verbatim
def r46Val : B128 := BitVec.ofNat 128 150254873993691350120483903676558564010

-- @@ L342-345 verbatim
noncomputable def r46 := toPoly r46Val
lemma step_46 : r45^2 = (toPoly (to256 q46Val)) * ghashPoly + r46 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r45Val q46Val r46Val; rfl -- Kernel check


-- @@ L347-347 verbatim
def q47Val : B128 := BitVec.ofNat 128 27918985595935424472919418209090736158

-- @@ L348-348 verbatim
def r47Val : B128 := BitVec.ofNat 128 233624311168361768088952357930788403998

-- @@ L349-352 verbatim
noncomputable def r47 := toPoly r47Val
lemma step_47 : r46^2 = (toPoly (to256 q47Val)) * ghashPoly + r47 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r46Val q47Val r47Val; rfl -- Kernel check


-- @@ L354-354 verbatim
def q48Val : B128 := BitVec.ofNat 128 90830471862246153247450751397716381795

-- @@ L355-355 verbatim
def r48Val : B128 := BitVec.ofNat 128 301852678830317075984151617556076790269

-- @@ L356-359 verbatim
noncomputable def r48 := toPoly r48Val
lemma step_48 : r47^2 = (toPoly (to256 q48Val)) * ghashPoly + r48 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r47Val q48Val r48Val; rfl -- Kernel check


-- @@ L361-361 verbatim
def q49Val : B128 := BitVec.ofNat 128 111681135018577110704347238966514418027

-- @@ L362-362 verbatim
def r49Val : B128 := BitVec.ofNat 128 334713874327018819147718792733305726656

-- @@ L363-366 verbatim
noncomputable def r49 := toPoly r49Val
lemma step_49 : r48^2 = (toPoly (to256 q49Val)) * ghashPoly + r49 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r48Val q49Val r49Val; rfl -- Kernel check


-- @@ L368-368 verbatim
def q50Val : B128 := BitVec.ofNat 128 113344277472022619116480485242451285306

-- @@ L369-369 verbatim
def r50Val : B128 := BitVec.ofNat 128 102613057823079007323731014766805608102

-- @@ L370-373 verbatim
noncomputable def r50 := toPoly r50Val
lemma step_50 : r49^2 = (toPoly (to256 q50Val)) * ghashPoly + r50 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r49Val q50Val r50Val; rfl -- Kernel check


-- @@ L375-375 verbatim
def q51Val : B128 := BitVec.ofNat 128 21688325726969315257874800492319691801

-- @@ L376-376 verbatim
def r51Val : B128 := BitVec.ofNat 128 102960897267461938273022342347012760795

-- @@ L377-380 verbatim
noncomputable def r51 := toPoly r51Val
lemma step_51 : r50^2 = (toPoly (to256 q51Val)) * ghashPoly + r51 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r50Val q51Val r51Val; rfl -- Kernel check


-- @@ L382-382 verbatim
def q52Val : B128 := BitVec.ofNat 128 21688651275484189220660633885066941725

-- @@ L383-383 verbatim
def r52Val : B128 := BitVec.ofNat 128 12615472659389050585944223579430941846

-- @@ L384-387 verbatim
noncomputable def r52 := toPoly r52Val
lemma step_52 : r51^2 = (toPoly (to256 q52Val)) * ghashPoly + r52 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r51Val q52Val r52Val; rfl -- Kernel check


-- @@ L389-389 verbatim
def q53Val : B128 := BitVec.ofNat 128 337931664957145912131522070333887569

-- @@ L390-390 verbatim
def r53Val : B128 := BitVec.ofNat 128 127982396443970808193093289421192168483

-- @@ L391-394 verbatim
noncomputable def r53 := toPoly r53Val
lemma step_53 : r52^2 = (toPoly (to256 q53Val)) * ghashPoly + r53 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r52Val q53Val r53Val; rfl -- Kernel check


-- @@ L396-396 verbatim
def q54Val : B128 := BitVec.ofNat 128 26584889524667542359832176840194131230

-- @@ L397-397 verbatim
def r54Val : B128 := BitVec.ofNat 128 80211020574021611523259929375765860447

-- @@ L398-401 verbatim
noncomputable def r54 := toPoly r54Val
lemma step_54 : r53^2 = (toPoly (to256 q54Val)) * ghashPoly + r54 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r53Val q54Val r54Val; rfl -- Kernel check


-- @@ L403-403 verbatim
def q55Val : B128 := BitVec.ofNat 128 7061873599502177810890797532710258006

-- @@ L404-404 verbatim
def r55Val : B128 := BitVec.ofNat 128 328306714951167239883061265636229931255

-- @@ L405-408 verbatim
noncomputable def r55 := toPoly r55Val
lemma step_55 : r54^2 = (toPoly (to256 q55Val)) * ghashPoly + r55 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r54Val q55Val r55Val; rfl -- Kernel check


-- @@ L410-410 verbatim
def q56Val : B128 := BitVec.ofNat 128 113089956021307759246001883954363240570

-- @@ L411-411 verbatim
def r56Val : B128 := BitVec.ofNat 128 154202500596702199027624208412024772979

-- @@ L412-415 verbatim
noncomputable def r56 := toPoly r56Val
lemma step_56 : r55^2 = (toPoly (to256 q56Val)) * ghashPoly + r56 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r55Val q56Val r56Val; rfl -- Kernel check


-- @@ L417-417 verbatim
def q57Val : B128 := BitVec.ofNat 128 27996864983398597151662045814934552847

-- @@ L418-418 verbatim
def r57Val : B128 := BitVec.ofNat 128 243851091912831247504069218024646202792

-- @@ L419-422 verbatim
noncomputable def r57 := toPoly r57Val
lemma step_57 : r56^2 = (toPoly (to256 q57Val)) * ghashPoly + r57 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r56Val q57Val r57Val; rfl -- Kernel check


-- @@ L424-424 verbatim
def q58Val : B128 := BitVec.ofNat 128 91826197141446752898753407217650974759

-- @@ L425-425 verbatim
def r58Val : B128 := BitVec.ofNat 128 27440791048182847192756476088690644789

-- @@ L426-429 verbatim
noncomputable def r58 := toPoly r58Val
lemma step_58 : r57^2 = (toPoly (to256 q58Val)) * ghashPoly + r58 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r57Val q58Val r58Val; rfl -- Kernel check


-- @@ L431-431 verbatim
def q59Val : B128 := BitVec.ofNat 128 1413685243047349389981581478196429825

-- @@ L432-432 verbatim
def r59Val : B128 := BitVec.ofNat 128 211387903213242387898935001709526309270

-- @@ L433-436 verbatim
noncomputable def r59 := toPoly r59Val
lemma step_59 : r58^2 = (toPoly (to256 q59Val)) * ghashPoly + r59 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r58Val q59Val r59Val; rfl -- Kernel check


-- @@ L438-438 verbatim
def q60Val : B128 := BitVec.ofNat 128 86841166647874110313667572945145627760

-- @@ L439-439 verbatim
def r60Val : B128 := BitVec.ofNat 128 159829576190644668190096436593299055684

-- @@ L440-443 verbatim
noncomputable def r60 := toPoly r60Val
lemma step_60 : r59^2 = (toPoly (to256 q60Val)) * ghashPoly + r60 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r59Val q60Val r60Val; rfl -- Kernel check


-- @@ L445-445 verbatim
def q61Val : B128 := BitVec.ofNat 128 28246202977744983831384242042349896718

-- @@ L446-446 verbatim
def r61Val : B128 := BitVec.ofNat 128 211134062703199012190249497033863383866

-- @@ L447-450 verbatim
noncomputable def r61 := toPoly r61Val
lemma step_61 : r60^2 = (toPoly (to256 q61Val)) * ghashPoly + r61 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r60Val q61Val r61Val; rfl -- Kernel check


-- @@ L452-452 verbatim
def q62Val : B128 := BitVec.ofNat 128 86837617148184232060666537332607095093

-- @@ L453-453 verbatim
def r62Val : B128 := BitVec.ofNat 128 82185866721533220436512213066902333519

-- @@ L454-457 verbatim
noncomputable def r62 := toPoly r62Val
lemma step_62 : r61^2 = (toPoly (to256 q62Val)) * ghashPoly + r62 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r61Val q62Val r62Val; rfl -- Kernel check


-- @@ L459-459 verbatim
def q63Val : B128 := BitVec.ofNat 128 7068360173580815494096880910548145427

-- @@ L460-460 verbatim
def r63Val : B128 := BitVec.ofNat 128 327395961906668187682165754937045283500

-- @@ L461-464 verbatim
noncomputable def r63 := toPoly r63Val
lemma step_63 : r62^2 = (toPoly (to256 q63Val)) * ghashPoly + r63 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r62Val q63Val r63Val; rfl -- Kernel check


-- @@ L466-466 verbatim
def q64Val : B128 := BitVec.ofNat 128 113088556753929231734156930669399326778

-- @@ L467-467 verbatim
def r64Val : B128 := BitVec.ofNat 128 129460184901158119860735353079755610614

-- @@ L468-471 verbatim
noncomputable def r64 := toPoly r64Val
lemma step_64 : r63^2 = (toPoly (to256 q64Val)) * ghashPoly + r64 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r63Val q64Val r64Val; rfl -- Kernel check


-- @@ L473-473 verbatim
def q65Val : B128 := BitVec.ofNat 128 26590159208040329700719228969042593099

-- @@ L474-474 verbatim
def r65Val : B128 := BitVec.ofNat 128 165640453935684170557382138895643060837

-- @@ L475-478 verbatim
noncomputable def r65 := toPoly r65Val
lemma step_65 : r64^2 = (toPoly (to256 q65Val)) * ghashPoly + r65 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r64Val q65Val r65Val; rfl -- Kernel check


-- @@ L480-480 verbatim
def q66Val : B128 := BitVec.ofNat 128 28330496435819242658153112454463574031

-- @@ L481-481 verbatim
def r66Val : B128 := BitVec.ofNat 128 258895673196720778598706762360552858556

-- @@ L482-485 verbatim
noncomputable def r66 := toPoly r66Val
lemma step_66 : r65^2 = (toPoly (to256 q66Val)) * ghashPoly + r66 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r65Val q66Val r66Val; rfl -- Kernel check


-- @@ L487-487 verbatim
def q67Val : B128 := BitVec.ofNat 128 106360632796475222630177185573960421676

-- @@ L488-488 verbatim
def r67Val : B128 := BitVec.ofNat 128 301930392259976828106625834641931740308

-- @@ L489-492 verbatim
noncomputable def r67 := toPoly r67Val
lemma step_67 : r66^2 = (toPoly (to256 q67Val)) * ghashPoly + r67 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r66Val q67Val r67Val; rfl -- Kernel check


-- @@ L494-494 verbatim
def q68Val : B128 := BitVec.ofNat 128 111681195627886010777831830863322830206

-- @@ L495-495 verbatim
def r68Val : B128 := BitVec.ofNat 128 254590090333913220966971847449742103658

-- @@ L496-499 verbatim
noncomputable def r68 := toPoly r68Val
lemma step_68 : r67^2 = (toPoly (to256 q68Val)) * ghashPoly + r68 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r67Val q68Val r68Val; rfl -- Kernel check


-- @@ L501-501 verbatim
def q69Val : B128 := BitVec.ofNat 128 92159380091923100147260900319429678434

-- @@ L502-502 verbatim
def r69Val : B128 := BitVec.ofNat 128 154605543219637426435106976091970670442

-- @@ L503-506 verbatim
noncomputable def r69 := toPoly r69Val
lemma step_69 : r68^2 = (toPoly (to256 q69Val)) * ghashPoly + r69 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r68Val q69Val r69Val; rfl -- Kernel check


-- @@ L508-508 verbatim
def q70Val : B128 := BitVec.ofNat 128 27997195940475076739387703229219689547

-- @@ L509-509 verbatim
def r70Val : B128 := BitVec.ofNat 128 328554470600989978311552677909447941173

-- @@ L510-513 verbatim
noncomputable def r70 := toPoly r70Val
lemma step_70 : r69^2 = (toPoly (to256 q70Val)) * ghashPoly + r70 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r69Val q70Val r70Val; rfl -- Kernel check


-- @@ L515-515 verbatim
def q71Val : B128 := BitVec.ofNat 128 113093505427900630694337031647284712575

-- @@ L516-516 verbatim
def r71Val : B128 := BitVec.ofNat 128 66427334083092228965437207507360258028

-- @@ L517-520 verbatim
noncomputable def r71 := toPoly r71Val
lemma step_71 : r70^2 = (toPoly (to256 q71Val)) * ghashPoly + r71 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r70Val q71Val r71Val; rfl -- Kernel check


-- @@ L522-522 verbatim
def q72Val : B128 := BitVec.ofNat 128 6653061436929269215650648925752610883

-- @@ L523-523 verbatim
def r72Val : B128 := BitVec.ofNat 128 269818012861271281423176274446422361113

-- @@ L524-527 verbatim
noncomputable def r72 := toPoly r72Val
lemma step_72 : r71^2 = (toPoly (to256 q72Val)) * ghashPoly + r72 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r71Val q72Val r72Val; rfl -- Kernel check


-- @@ L529-529 verbatim
def q73Val : B128 := BitVec.ofNat 128 106693046271573877075738515171988297017

-- @@ L530-530 verbatim
def r73Val : B128 := BitVec.ofNat 128 264132206416858785477441377236972222062

-- @@ L531-534 verbatim
noncomputable def r73 := toPoly r73Val
lemma step_73 : r72^2 = (toPoly (to256 q73Val)) * ghashPoly + r73 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r72Val q73Val r73Val; rfl -- Kernel check


-- @@ L536-536 verbatim
def q74Val : B128 := BitVec.ofNat 128 106443486670795937264113025222060609657

-- @@ L537-537 verbatim
def r74Val : B128 := BitVec.ofNat 128 334025740161143946608295602721698306491

-- @@ L538-541 verbatim
noncomputable def r74 := toPoly r74Val
lemma step_74 : r73^2 = (toPoly (to256 q74Val)) * ghashPoly + r74 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r73Val q74Val r74Val; rfl -- Kernel check


-- @@ L543-543 verbatim
def q75Val : B128 := BitVec.ofNat 128 113342978110273067672708979424336364922

-- @@ L544-544 verbatim
def r75Val : B128 := BitVec.ofNat 128 122383803109284106894334171034010591779

-- @@ L545-548 verbatim
noncomputable def r75 := toPoly r75Val
lemma step_75 : r74^2 = (toPoly (to256 q75Val)) * ghashPoly + r75 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r74Val q75Val r75Val; rfl -- Kernel check


-- @@ L550-550 verbatim
def q76Val : B128 := BitVec.ofNat 128 23012280281306496098841036354677392648

-- @@ L551-551 verbatim
def r76Val : B128 := BitVec.ofNat 128 296025850348968698648586558724418263869

-- @@ L552-555 verbatim
noncomputable def r76 := toPoly r76Val
lemma step_76 : r75^2 = (toPoly (to256 q76Val)) * ghashPoly + r76 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r75Val q76Val r76Val; rfl -- Kernel check


-- @@ L557-557 verbatim
def q77Val : B128 := BitVec.ofNat 128 108105021368416688828337788080635253053

-- @@ L558-558 verbatim
def r77Val : B128 := BitVec.ofNat 128 37960944824515205685591230648204258402

-- @@ L559-562 verbatim
noncomputable def r77 := toPoly r77Val
lemma step_77 : r76^2 = (toPoly (to256 q77Val)) * ghashPoly + r77 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r76Val q77Val r77Val; rfl -- Kernel check


-- @@ L564-564 verbatim
def q78Val : B128 := BitVec.ofNat 128 1745916553082199154939513287878906948

-- @@ L565-565 verbatim
def r78Val : B128 := BitVec.ofNat 128 226742293150914418175831072849372273624

-- @@ L566-569 verbatim
noncomputable def r78 := toPoly r78Val
lemma step_78 : r77^2 = (toPoly (to256 q78Val)) * ghashPoly + r78 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r77Val q78Val r78Val; rfl -- Kernel check


-- @@ L571-571 verbatim
def q79Val : B128 := BitVec.ofNat 128 90741899550417938157404566366188802402

-- @@ L572-572 verbatim
def r79Val : B128 := BitVec.ofNat 128 248467511393027050396179622604745119342

-- @@ L573-576 verbatim
noncomputable def r79 := toPoly r79Val
lemma step_79 : r78^2 = (toPoly (to256 q79Val)) * ghashPoly + r79 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r78Val q79Val r79Val; rfl -- Kernel check


-- @@ L578-578 verbatim
def q80Val : B128 := BitVec.ofNat 128 92071518035819132161895892174899593314

-- @@ L579-579 verbatim
def r80Val : B128 := BitVec.ofNat 128 161687256048543766767383987762312963194

-- @@ L580-583 verbatim
noncomputable def r80 := toPoly r80Val
lemma step_80 : r79^2 = (toPoly (to256 q80Val)) * ghashPoly + r80 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r79Val q80Val r80Val; rfl -- Kernel check


-- @@ L585-585 verbatim
def q81Val : B128 := BitVec.ofNat 128 28252666832370719236803303807264036127

-- @@ L586-586 verbatim
def r81Val : B128 := BitVec.ofNat 128 269110802679140966820977389101215773081

-- @@ L587-590 verbatim
noncomputable def r81 := toPoly r81Val
lemma step_81 : r80^2 = (toPoly (to256 q81Val)) * ghashPoly + r81 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r80Val q81Val r81Val; rfl -- Kernel check


-- @@ L592-592 verbatim
def q82Val : B128 := BitVec.ofNat 128 106691743072576809547238840914556290412

-- @@ L593-593 verbatim
def r82Val : B128 := BitVec.ofNat 128 195167772352272279581770856328715365701

-- @@ L594-597 verbatim
noncomputable def r82 := toPoly r82Val
lemma step_82 : r81^2 = (toPoly (to256 q82Val)) * ghashPoly + r82 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r81Val q82Val r82Val; rfl -- Kernel check


-- @@ L599-599 verbatim
def q83Val : B128 := BitVec.ofNat 128 86422232211083446865462163070649439524

-- @@ L600-600 verbatim
def r83Val : B128 := BitVec.ofNat 128 6839019468748781921035578916625770989

-- @@ L601-604 verbatim
noncomputable def r83 := toPoly r83Val
lemma step_83 : r82^2 = (toPoly (to256 q83Val)) * ghashPoly + r83 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r82Val q83Val r83Val; rfl -- Kernel check


-- @@ L606-606 verbatim
def q84Val : B128 := BitVec.ofNat 128 88351524371087060277032187079229461

-- @@ L607-607 verbatim
def r84Val : B128 := BitVec.ofNat 128 119133456490525504919656485393064943290

-- @@ L608-611 verbatim
noncomputable def r84 := toPoly r84Val
lemma step_84 : r83^2 = (toPoly (to256 q84Val)) * ghashPoly + r84 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r83Val q84Val r84Val; rfl -- Kernel check


-- @@ L613-613 verbatim
def q85Val : B128 := BitVec.ofNat 128 22935754432972881912600091642172883273

-- @@ L614-614 verbatim
def r85Val : B128 := BitVec.ofNat 128 284976786280009736580048287615377352507

-- @@ L615-618 verbatim
noncomputable def r85 := toPoly r85Val
lemma step_85 : r84^2 = (toPoly (to256 q85Val)) * ghashPoly + r85 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r84Val q85Val r85Val; rfl -- Kernel check


-- @@ L620-620 verbatim
def q86Val : B128 := BitVec.ofNat 128 107771720531476048881238081762006946940

-- @@ L621-621 verbatim
def r86Val : B128 := BitVec.ofNat 128 53368461820224018424322992725600146993

-- @@ L622-625 verbatim
noncomputable def r86 := toPoly r86Val
lemma step_86 : r85^2 = (toPoly (to256 q86Val)) * ghashPoly + r86 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r85Val q86Val r86Val; rfl -- Kernel check


-- @@ L627-627 verbatim
def q87Val : B128 := BitVec.ofNat 128 5649301702496680664927320601070403923

-- @@ L628-628 verbatim
def r87Val : B128 := BitVec.ofNat 128 165521487478005576843608560748526611000

-- @@ L629-632 verbatim
noncomputable def r87 := toPoly r87Val
lemma step_87 : r86^2 = (toPoly (to256 q87Val)) * ghashPoly + r87 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r86Val q87Val r87Val; rfl -- Kernel check


-- @@ L634-634 verbatim
def q88Val : B128 := BitVec.ofNat 128 28330471323921145967809237462456554778

-- @@ L635-635 verbatim
def r88Val : B128 := BitVec.ofNat 128 195068410978310211650239904624548258566

-- @@ L636-639 verbatim
noncomputable def r88 := toPoly r88Val
lemma step_88 : r87^2 = (toPoly (to256 q88Val)) * ghashPoly + r88 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r87Val q88Val r88Val; rfl -- Kernel check


-- @@ L641-641 verbatim
def q89Val : B128 := BitVec.ofNat 128 86422211531083546570630185816972149872

-- @@ L642-642 verbatim
def r89Val : B128 := BitVec.ofNat 128 113589941149803520359128394698002916676

-- @@ L643-646 verbatim
noncomputable def r89 := toPoly r89Val
lemma step_89 : r88^2 = (toPoly (to256 q89Val)) * ghashPoly + r89 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r88Val q89Val r89Val; rfl -- Kernel check


-- @@ L648-648 verbatim
def q90Val : B128 := BitVec.ofNat 128 22685572194236020141428944940093998365

-- @@ L649-649 verbatim
def r90Val : B128 := BitVec.ofNat 128 249467295398400182484435455780551427523

-- @@ L650-653 verbatim
noncomputable def r90 := toPoly r90Val
lemma step_90 : r89^2 = (toPoly (to256 q90Val)) * ghashPoly + r90 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r89Val q90Val r90Val; rfl -- Kernel check


-- @@ L655-655 verbatim
def q91Val : B128 := BitVec.ofNat 128 92076385834802754365670188026180227442

-- @@ L656-656 verbatim
def r91Val : B128 := BitVec.ofNat 128 75006380269635190750556711265086168923

-- @@ L657-660 verbatim
noncomputable def r91 := toPoly r91Val
lemma step_91 : r90^2 = (toPoly (to256 q91Val)) * ghashPoly + r91 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r90Val q91Val r91Val; rfl -- Kernel check


-- @@ L662-662 verbatim
def q92Val : B128 := BitVec.ofNat 128 6978859064917858239407404423466729542

-- @@ L663-663 verbatim
def r92Val : B128 := BitVec.ofNat 128 318824008587287836741888684444380361623

-- @@ L664-667 verbatim
noncomputable def r92 := toPoly r92Val
lemma step_92 : r91^2 = (toPoly (to256 q92Val)) * ghashPoly + r92 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r91Val q92Val r92Val; rfl -- Kernel check


-- @@ L669-669 verbatim
def q93Val : B128 := BitVec.ofNat 128 112098145225801890397053623176863679546

-- @@ L670-670 verbatim
def r93Val : B128 := BitVec.ofNat 128 178459331004814995506250383468567150771

-- @@ L671-674 verbatim
noncomputable def r93 := toPoly r93Val
lemma step_93 : r92^2 = (toPoly (to256 q93Val)) * ghashPoly + r93 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r92Val q93Val r93Val; rfl -- Kernel check


-- @@ L676-676 verbatim
def q94Val : B128 := BitVec.ofNat 128 85174762502891044365941082238663790704

-- @@ L677-677 verbatim
def r94Val : B128 := BitVec.ofNat 128 211872363948266361377324272839095225429

-- @@ L678-681 verbatim
noncomputable def r94 := toPoly r94Val
lemma step_94 : r93^2 = (toPoly (to256 q94Val)) * ghashPoly + r94 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r93Val q94Val r94Val; rfl -- Kernel check


-- @@ L683-683 verbatim
def q95Val : B128 := BitVec.ofNat 128 86841571955308605099847419267740865588

-- @@ L684-684 verbatim
def r95Val : B128 := BitVec.ofNat 128 143811789042420870636385239690585466781

-- @@ L685-688 verbatim
noncomputable def r95 := toPoly r95Val
lemma step_95 : r94^2 = (toPoly (to256 q95Val)) * ghashPoly + r95 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r94Val q95Val r95Val; rfl -- Kernel check


-- @@ L690-690 verbatim
def q96Val : B128 := BitVec.ofNat 128 27000045156914888433990455064947393806

-- @@ L691-691 verbatim
def r96Val : B128 := BitVec.ofNat 128 86248589110002907259851524152594849147

-- @@ L692-695 verbatim
noncomputable def r96 := toPoly r96Val
lemma step_96 : r95^2 = (toPoly (to256 q96Val)) * ghashPoly + r96 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r95Val q96Val r96Val; rfl -- Kernel check


-- @@ L697-697 verbatim
def q97Val : B128 := BitVec.ofNat 128 21269351997049433062953149265858285644

-- @@ L698-698 verbatim
def r97Val : B128 := BitVec.ofNat 128 44507931730853748353717482469352571553

-- @@ L699-702 verbatim
noncomputable def r97 := toPoly r97Val
lemma step_97 : r96^2 = (toPoly (to256 q97Val)) * ghashPoly + r97 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r96Val q97Val r97Val; rfl -- Kernel check


-- @@ L704-704 verbatim
def q98Val : B128 := BitVec.ofNat 128 5322535703422135752597822652532412743

-- @@ L705-705 verbatim
def r98Val : B128 := BitVec.ofNat 128 32963873827986936976259691565938463060

-- @@ L706-709 verbatim
noncomputable def r98 := toPoly r98Val
lemma step_98 : r97^2 = (toPoly (to256 q98Val)) * ghashPoly + r98 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r97Val q98Val r98Val; rfl -- Kernel check


-- @@ L711-711 verbatim
def q99Val : B128 := BitVec.ofNat 128 1663163945965777307793753184466715668

-- @@ L712-712 verbatim
def r99Val : B128 := BitVec.ofNat 128 216630587467047648990556766097492264828

-- @@ L713-716 verbatim
noncomputable def r99 := toPoly r99Val
lemma step_99 : r98^2 = (toPoly (to256 q99Val)) * ghashPoly + r99 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r98Val q99Val r99Val; rfl -- Kernel check


-- @@ L718-718 verbatim
def q100Val : B128 := BitVec.ofNat 128 90410002075340011635962445654417232183

-- @@ L719-719 verbatim
def r100Val : B128 := BitVec.ofNat 128 185272067944601170075289186680278366549

-- @@ L720-723 verbatim
noncomputable def r100 := toPoly r100Val
lemma step_100 : r99^2 = (toPoly (to256 q100Val)) * ghashPoly + r100 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r99Val q100Val r100Val; rfl -- Kernel check


-- @@ L725-725 verbatim
def q101Val : B128 := BitVec.ofNat 128 85429266178969957737271708988624688160

-- @@ L726-726 verbatim
def r101Val : B128 := BitVec.ofNat 128 220985417642294560069226125886699449841

-- @@ L727-730 verbatim
noncomputable def r101 := toPoly r101Val
lemma step_101 : r100^2 = (toPoly (to256 q101Val)) * ghashPoly + r101 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r100Val q101Val r101Val; rfl -- Kernel check


-- @@ L732-732 verbatim
def q102Val : B128 := BitVec.ofNat 128 90491674170747685916512986686148334707

-- @@ L733-733 verbatim
def r102Val : B128 := BitVec.ofNat 128 264688778274977021302766754871988896216

-- @@ L734-737 verbatim
noncomputable def r102 := toPoly r102Val
lemma step_102 : r101^2 = (toPoly (to256 q102Val)) * ghashPoly + r102 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r101Val q102Val r102Val; rfl -- Kernel check


-- @@ L739-739 verbatim
def q103Val : B128 := BitVec.ofNat 128 106447359107255926573111061020838724904

-- @@ L740-740 verbatim
def r103Val : B128 := BitVec.ofNat 128 333264177890741770072193430405525003928

-- @@ L741-744 verbatim
noncomputable def r103 := toPoly r103Val
lemma step_103 : r102^2 = (toPoly (to256 q103Val)) * ghashPoly + r103 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r102Val q103Val r103Val; rfl -- Kernel check


-- @@ L746-746 verbatim
def q104Val : B128 := BitVec.ofNat 128 113338860390302193732750644424425424250

-- @@ L747-747 verbatim
def r104Val : B128 := BitVec.ofNat 128 33205950964766484238866480871644341798

-- @@ L748-751 verbatim
noncomputable def r104 := toPoly r104Val
lemma step_104 : r103^2 = (toPoly (to256 q104Val)) * ghashPoly + r104 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r103Val q104Val r104Val; rfl -- Kernel check


-- @@ L753-753 verbatim
def q105Val : B128 := BitVec.ofNat 128 1663264467921888622614922324832748865

-- @@ L754-754 verbatim
def r105Val : B128 := BitVec.ofNat 128 301310530123703810140221288298382736979

-- @@ L755-758 verbatim
noncomputable def r105 := toPoly r105Val
lemma step_105 : r104^2 = (toPoly (to256 q105Val)) * ghashPoly + r105 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r104Val q105Val r105Val; rfl -- Kernel check


-- @@ L760-760 verbatim
def q106Val : B128 := BitVec.ofNat 128 111677306697434252276890411435311514938

-- @@ L761-761 verbatim
def r106Val : B128 := BitVec.ofNat 128 254546671986439821273357947065150691235

-- @@ L762-765 verbatim
noncomputable def r106 := toPoly r106Val
lemma step_106 : r105^2 = (toPoly (to256 q106Val)) * ghashPoly + r106 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r105Val q106Val r106Val; rfl -- Kernel check


-- @@ L767-767 verbatim
def q107Val : B128 := BitVec.ofNat 128 92158509633152670942014662830365885751

-- @@ L768-768 verbatim
def r107Val : B128 := BitVec.ofNat 128 154463474563896264286711223429656871936

-- @@ L769-772 verbatim
noncomputable def r107 := toPoly r107Val
lemma step_107 : r106^2 = (toPoly (to256 q107Val)) * ghashPoly + r107 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r106Val q107Val r107Val; rfl -- Kernel check


-- @@ L774-774 verbatim
def q108Val : B128 := BitVec.ofNat 128 27996967361055562314451527514068107615

-- @@ L775-775 verbatim
def r108Val : B128 := BitVec.ofNat 128 238553731111275542579218303752720181533

-- @@ L776-779 verbatim
noncomputable def r108 := toPoly r108Val
lemma step_108 : r107^2 = (toPoly (to256 q108Val)) * ghashPoly + r108 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r107Val q108Val r108Val; rfl -- Kernel check


-- @@ L781-781 verbatim
def q109Val : B128 := BitVec.ofNat 128 91743120812629147377374904346117947762

-- @@ L782-782 verbatim
def r109Val : B128 := BitVec.ofNat 128 18384089493480778990035902178609102351

-- @@ L783-786 verbatim
noncomputable def r109 := toPoly r109Val
lemma step_109 : r108^2 = (toPoly (to256 q109Val)) * ghashPoly + r109 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r108Val q109Val r109Val; rfl -- Kernel check


-- @@ L788-788 verbatim
def q110Val : B128 := BitVec.ofNat 128 422220209435656804352068862373532753

-- @@ L789-789 verbatim
def r110Val : B128 := BitVec.ofNat 128 75820400037257621222803633372476097890

-- @@ L790-793 verbatim
noncomputable def r110 := toPoly r110Val
lemma step_110 : r109^2 = (toPoly (to256 q110Val)) * ghashPoly + r110 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r109Val q110Val r110Val; rfl -- Kernel check


-- @@ L795-795 verbatim
def q111Val : B128 := BitVec.ofNat 128 6983644668825866946112147987807354946

-- @@ L796-796 verbatim
def r111Val : B128 := BitVec.ofNat 128 317696663419018730218660346852253168842

-- @@ L797-800 verbatim
noncomputable def r111 := toPoly r111Val
lemma step_111 : r110^2 = (toPoly (to256 q111Val)) * ghashPoly + r111 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r110Val q111Val r111Val; rfl -- Kernel check


-- @@ L802-802 verbatim
def q112Val : B128 := BitVec.ofNat 128 112096497197083545190001414019926261867

-- @@ L803-803 verbatim
def r112Val : B128 := BitVec.ofNat 128 265151192445743918497476159262292403413

-- @@ L804-807 verbatim
noncomputable def r112 := toPoly r112Val
lemma step_112 : r111^2 = (toPoly (to256 q112Val)) * ghashPoly + r112 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r111Val q112Val r112Val; rfl -- Kernel check


-- @@ L809-809 verbatim
def q113Val : B128 := BitVec.ofNat 128 106447709219897039649066968929207930925

-- @@ L810-810 verbatim
def r113Val : B128 := BitVec.ofNat 128 227243742383211985895879960446026839890

-- @@ L811-814 verbatim
noncomputable def r113 := toPoly r113Val
lemma step_113 : r112^2 = (toPoly (to256 q113Val)) * ghashPoly + r113 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r112Val q113Val r113Val; rfl -- Kernel check


-- @@ L816-816 verbatim
def q114Val : B128 := BitVec.ofNat 128 90742305271354986935977381436566077815

-- @@ L817-817 verbatim
def r114Val : B128 := BitVec.ofNat 128 253422517028958359388508295558326299841

-- @@ L818-821 verbatim
noncomputable def r114 := toPoly r114Val
lemma step_114 : r113^2 = (toPoly (to256 q114Val)) * ghashPoly + r114 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r113Val q114Val r114Val; rfl -- Kernel check


-- @@ L823-823 verbatim
def q115Val : B128 := BitVec.ofNat 128 92154265519134838446371680302547358755

-- @@ L824-824 verbatim
def r115Val : B128 := BitVec.ofNat 128 150927228725920353331738429768615062888

-- @@ L825-828 verbatim
noncomputable def r115 := toPoly r115Val
lemma step_115 : r114^2 = (toPoly (to256 q115Val)) * ghashPoly + r115 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r114Val q115Val r115Val; rfl -- Kernel check


-- @@ L830-830 verbatim
def q116Val : B128 := BitVec.ofNat 128 27920283769131231470092830173402764319

-- @@ L831-831 verbatim
def r116Val : B128 := BitVec.ofNat 128 313214421372485833387472208663997282205

-- @@ L832-835 verbatim
noncomputable def r116 := toPoly r116Val
lemma step_116 : r115^2 = (toPoly (to256 q116Val)) * ghashPoly + r116 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r115Val q116Val r116Val; rfl -- Kernel check


-- @@ L837-837 verbatim
def q117Val : B128 := BitVec.ofNat 128 112014799675959688252580459700414321791

-- @@ L838-838 verbatim
def r117Val : B128 := BitVec.ofNat 128 205270197963465857064863719867483624364

-- @@ L839-842 verbatim
noncomputable def r117 := toPoly r117Val
lemma step_117 : r116^2 = (toPoly (to256 q117Val)) * ghashPoly + r117 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r116Val q117Val r117Val; rfl -- Kernel check


-- @@ L844-844 verbatim
def q118Val : B128 := BitVec.ofNat 128 86753307998271888269735528725523529828

-- @@ L845-845 verbatim
def r118Val : B128 := BitVec.ofNat 128 64566217092196733533220887167246694252

-- @@ L846-849 verbatim
noncomputable def r118 := toPoly r118Val
lemma step_118 : r117^2 = (toPoly (to256 q118Val)) * ghashPoly + r118 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r117Val q118Val r118Val; rfl -- Kernel check


-- @@ L851-851 verbatim
def q119Val : B128 := BitVec.ofNat 128 6647458731689705241109357448167490823

-- @@ L852-852 verbatim
def r119Val : B128 := BitVec.ofNat 128 296938408697389789750215214903058009285

-- @@ L853-856 verbatim
noncomputable def r119 := toPoly r119Val
lemma step_119 : r118^2 = (toPoly (to256 q119Val)) * ghashPoly + r119 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r118Val q119Val r119Val; rfl -- Kernel check


-- @@ L858-858 verbatim
def q120Val : B128 := BitVec.ofNat 128 108109219812349672459520657510902285624

-- @@ L859-859 verbatim
def r120Val : B128 := BitVec.ofNat 128 10807226621238021931262095742919972793

-- @@ L860-863 verbatim
noncomputable def r120 := toPoly r120Val
lemma step_120 : r119^2 = (toPoly (to256 q120Val)) * ghashPoly + r120 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r119Val q120Val r120Val; rfl -- Kernel check


-- @@ L865-865 verbatim
def q121Val : B128 := BitVec.ofNat 128 332388214023153671265224035075708225

-- @@ L866-866 verbatim
def r121Val : B128 := BitVec.ofNat 128 129631382596958590886433730895748353798

-- @@ L867-870 verbatim
noncomputable def r121 := toPoly r121Val
lemma step_121 : r120^2 = (toPoly (to256 q121Val)) * ghashPoly + r121 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r120Val q121Val r121Val; rfl -- Kernel check


-- @@ L872-872 verbatim
def q122Val : B128 := BitVec.ofNat 128 26591051871721900988471200547568947211

-- @@ L873-873 verbatim
def r122Val : B128 := BitVec.ofNat 128 59414367279926819390058891142076462501

-- @@ L874-877 verbatim
noncomputable def r122 := toPoly r122Val
lemma step_122 : r121^2 = (toPoly (to256 q122Val)) * ghashPoly + r122 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r121Val q122Val r122Val; rfl -- Kernel check


-- @@ L879-879 verbatim
def q123Val : B128 := BitVec.ofNat 128 5733695559838859821997752053717537795

-- @@ L880-880 verbatim
def r123Val : B128 := BitVec.ofNat 128 70216996008105906389747657374764050840

-- @@ L881-884 verbatim
noncomputable def r123 := toPoly r123Val
lemma step_123 : r122^2 = (toPoly (to256 q123Val)) * ghashPoly + r123 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r122Val q123Val r123Val; rfl -- Kernel check


-- @@ L886-886 verbatim
def q124Val : B128 := BitVec.ofNat 128 6730860005029551728181658353192424518

-- @@ L887-887 verbatim
def r124Val : B128 := BitVec.ofNat 128 264664062837534286517811593844813647762

-- @@ L888-891 verbatim
noncomputable def r124 := toPoly r124Val
lemma step_124 : r123^2 = (toPoly (to256 q124Val)) * ghashPoly + r124 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r123Val q124Val r124Val; rfl -- Kernel check


-- @@ L893-893 verbatim
def q125Val : B128 := BitVec.ofNat 128 106447304523985878018959366555039962424

-- @@ L894-894 verbatim
def r125Val : B128 := BitVec.ofNat 128 313275912279873968957145467509231826604

-- @@ L895-898 verbatim
noncomputable def r125 := toPoly r125Val
lemma step_125 : r124^2 = (toPoly (to256 q125Val)) * ghashPoly + r125 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r124Val q125Val r125Val; rfl -- Kernel check


-- @@ L900-900 verbatim
def q126Val : B128 := BitVec.ofNat 128 112014806009646954068650741980837728622

-- @@ L901-901 verbatim
def r126Val : B128 := BitVec.ofNat 128 205249681632336591850764335734481569114

-- @@ L902-905 verbatim
noncomputable def r126 := toPoly r126Val
lemma step_126 : r125^2 = (toPoly (to256 q126Val)) * ghashPoly + r126 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r125Val q126Val r126Val; rfl -- Kernel check


-- @@ L907-907 verbatim
def q127Val : B128 := BitVec.ofNat 128 86753306731492003871963199800359261216

-- @@ L908-908 verbatim
def r127Val : B128 := BitVec.ofNat 128 48611766702991209068831621643639680420

-- @@ L909-912 verbatim
noncomputable def r127 := toPoly r127Val
lemma step_127 : r126^2 = (toPoly (to256 q127Val)) * ghashPoly + r127 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r126Val q127Val r127Val; rfl -- Kernel check


-- @@ L914-914 verbatim
def q128Val : B128 := BitVec.ofNat 128 5401307411443467674021819165583622406

-- @@ L915-915 verbatim
def r128Val : B128 := BitVec.ofNat 128 2

-- @@ L916-919 verbatim
noncomputable def r128 := toPoly r128Val
lemma step_128 : r127^2 = (toPoly (to256 q128Val)) * ghashPoly + r128 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r127Val q128Val r128Val; rfl -- Kernel check


-- @@ L921-996 verbatim
/-- Intermediate Result: X^(2^64) mod P. Needed for GCD check. -/
theorem X_pow_2_pow_64_eq : (X : Polynomial (ZMod 2))^(2^64) % ghashPoly
    = toPoly (BitVec.ofNat 128 129460184901158119860735353079755610614) := by
  have s0 : X^(2^0) % ghashPoly = r0 % ghashPoly := by rw [pow_zero, pow_one, r0, X_ZMod2Poly_eq_X]
  have s1 := chain_step s0 step_1
  have s2 := chain_step s1 step_2
  have s3 := chain_step s2 step_3
  have s4 := chain_step s3 step_4
  have s5 := chain_step s4 step_5
  have s6 := chain_step s5 step_6
  have s7 := chain_step s6 step_7
  have s8 := chain_step s7 step_8
  have s9 := chain_step s8 step_9
  have s10 := chain_step s9 step_10
  have s11 := chain_step s10 step_11
  have s12 := chain_step s11 step_12
  have s13 := chain_step s12 step_13
  have s14 := chain_step s13 step_14
  have s15 := chain_step s14 step_15
  have s16 := chain_step s15 step_16
  have s17 := chain_step s16 step_17
  have s18 := chain_step s17 step_18
  have s19 := chain_step s18 step_19
  have s20 := chain_step s19 step_20
  have s21 := chain_step s20 step_21
  have s22 := chain_step s21 step_22
  have s23 := chain_step s22 step_23
  have s24 := chain_step s23 step_24
  have s25 := chain_step s24 step_25
  have s26 := chain_step s25 step_26
  have s27 := chain_step s26 step_27
  have s28 := chain_step s27 step_28
  have s29 := chain_step s28 step_29
  have s30 := chain_step s29 step_30
  have s31 := chain_step s30 step_31
  have s32 := chain_step s31 step_32
  have s33 := chain_step s32 step_33
  have s34 := chain_step s33 step_34
  have s35 := chain_step s34 step_35
  have s36 := chain_step s35 step_36
  have s37 := chain_step s36 step_37
  have s38 := chain_step s37 step_38
  have s39 := chain_step s38 step_39
  have s40 := chain_step s39 step_40
  have s41 := chain_step s40 step_41
  have s42 := chain_step s41 step_42
  have s43 := chain_step s42 step_43
  have s44 := chain_step s43 step_44
  have s45 := chain_step s44 step_45
  have s46 := chain_step s45 step_46
  have s47 := chain_step s46 step_47
  have s48 := chain_step s47 step_48
  have s49 := chain_step s48 step_49
  have s50 := chain_step s49 step_50
  have s51 := chain_step s50 step_51
  have s52 := chain_step s51 step_52
  have s53 := chain_step s52 step_53
  have s54 := chain_step s53 step_54
  have s55 := chain_step s54 step_55
  have s56 := chain_step s55 step_56
  have s57 := chain_step s56 step_57
  have s58 := chain_step s57 step_58
  have s59 := chain_step s58 step_59
  have s60 := chain_step s59 step_60
  have s61 := chain_step s60 step_61
  have s62 := chain_step s61 step_62
  have s63 := chain_step s62 step_63
  have s64 := chain_step s63 step_64
  rw [s64]
  rw [r64, r64Val]
  rw [Polynomial.mod_eq_self_iff]
  · -- Degree proof
    conv_rhs => rw [ghashPoly_degree]
    apply (toPoly_degree_lt_w (w := 128)
      (h_w_pos := by simp only [gt_iff_lt, Nat.ofNat_pos]) (v := r64Val))
  · exact ghashPoly_ne_zero


-- @@ L998-1079 verbatim
/-- Final Result: X^(2^128) = X (mod P). -/
theorem X_pow_2_pow_128_eq : (X : Polynomial (ZMod 2))^(2^128) % ghashPoly = X := by
  have hr64_mod : r64 % ghashPoly = r64 := by
    rw [r64, r64Val, Polynomial.mod_eq_self_iff]
    · conv_rhs => rw [ghashPoly_degree]
      exact (toPoly_degree_lt_w (w := 128)
        (h_w_pos := by simp only [gt_iff_lt, Nat.ofNat_pos]) (v := r64Val))
    · exact ghashPoly_ne_zero
  have s64 : X^(2^64) % ghashPoly = r64 % ghashPoly := by
    rw [hr64_mod]
    simpa [r64, r64Val] using X_pow_2_pow_64_eq
  have s65 := chain_step s64 step_65
  have s66 := chain_step s65 step_66
  have s67 := chain_step s66 step_67
  have s68 := chain_step s67 step_68
  have s69 := chain_step s68 step_69
  have s70 := chain_step s69 step_70
  have s71 := chain_step s70 step_71
  have s72 := chain_step s71 step_72
  have s73 := chain_step s72 step_73
  have s74 := chain_step s73 step_74
  have s75 := chain_step s74 step_75
  have s76 := chain_step s75 step_76
  have s77 := chain_step s76 step_77
  have s78 := chain_step s77 step_78
  have s79 := chain_step s78 step_79
  have s80 := chain_step s79 step_80
  have s81 := chain_step s80 step_81
  have s82 := chain_step s81 step_82
  have s83 := chain_step s82 step_83
  have s84 := chain_step s83 step_84
  have s85 := chain_step s84 step_85
  have s86 := chain_step s85 step_86
  have s87 := chain_step s86 step_87
  have s88 := chain_step s87 step_88
  have s89 := chain_step s88 step_89
  have s90 := chain_step s89 step_90
  have s91 := chain_step s90 step_91
  have s92 := chain_step s91 step_92
  have s93 := chain_step s92 step_93
  have s94 := chain_step s93 step_94
  have s95 := chain_step s94 step_95
  have s96 := chain_step s95 step_96
  have s97 := chain_step s96 step_97
  have s98 := chain_step s97 step_98
  have s99 := chain_step s98 step_99
  have s100 := chain_step s99 step_100
  have s101 := chain_step s100 step_101
  have s102 := chain_step s101 step_102
  have s103 := chain_step s102 step_103
  have s104 := chain_step s103 step_104
  have s105 := chain_step s104 step_105
  have s106 := chain_step s105 step_106
  have s107 := chain_step s106 step_107
  have s108 := chain_step s107 step_108
  have s109 := chain_step s108 step_109
  have s110 := chain_step s109 step_110
  have s111 := chain_step s110 step_111
  have s112 := chain_step s111 step_112
  have s113 := chain_step s112 step_113
  have s114 := chain_step s113 step_114
  have s115 := chain_step s114 step_115
  have s116 := chain_step s115 step_116
  have s117 := chain_step s116 step_117
  have s118 := chain_step s117 step_118
  have s119 := chain_step s118 step_119
  have s120 := chain_step s119 step_120
  have s121 := chain_step s120 step_121
  have s122 := chain_step s121 step_122
  have s123 := chain_step s122 step_123
  have s124 := chain_step s123 step_124
  have s125 := chain_step s124 step_125
  have s126 := chain_step s125 step_126
  have s127 := chain_step s126 step_127
  have s128 := chain_step s127 step_128

  rw [s128]
  have r128_eq_X : r128 = X := by
    rw [r128, r128Val]
    exact X_ZMod2Poly_eq_X
  rw [r128_eq_X]
  rw [X_mod_ghashPoly]


-- @@ L1081-1081 verbatim
end BF128Ghash
