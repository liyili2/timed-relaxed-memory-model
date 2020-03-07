theory AxiomaticSoundProof
imports Main SC11 AxiomaticModel
begin

locale axiomaticProof = axiomaticModel
begin

definition locMentioned where
"locMentioned T rho = {loc . \<exists> t tid aid . t \<in> T \<and> rho t = Some (tid,aid,Create loc)}"

definition modificationOrder where
"modificationOrder T rho x = {(a,b) . a \<in> T \<and> b \<in> T \<and> a < b \<and>
          (\<exists> tid1 aid1 tid2 aid2 ac1 ac2 . rho a = Some (tid1,aid1, ac1) \<and> rho b = Some (tid2,aid2,ac2)
             \<and> isWrite ac1 \<and> isWrite ac2 \<and> acLoc ac1 = Some x \<and> acLoc ac2 = Some x)}"

(*first, we prove that our model satisfies modification rules on all locations of all threads 
   it means that there is a modification order of writes on every location that no thread will violate. *)
lemma satMo : "\<forall> Tid T rho sb rf Locs . validExecution Tid T rho sb rf \<and> Locs = locMentioned T rho \<longrightarrow> 
               (\<forall> S x tid a b t1 t2 . S = observeMem Tid T rho sb rf Locs \<and>
                    (tid,a,x,Some t1) \<in> S \<and> (tid,b,x,Some t2) \<in> S \<and> a < b
                  \<longrightarrow> (t1 = t2 \<or> (t1,t2) \<in> (modificationOrder T rho x)))"
  apply simp
  sorry

(* second, we show that our model satisfy SRA model, with satMo lemma and sb U rf U Ux mo is acyclic. *)
definition acqRelAbove where
"acqRelAbove T rho = (\<forall> a tid aid ac . a \<in> T \<and> rho a = Some (tid,aid,ac) \<and> \<not> isFenceLike ac
                     \<longrightarrow> hasAtLeastAcqRel ac)"

definition moUnion where
"moUnion T rho Locs = {(a,b) . (\<exists> x \<in> Locs . (a,b) \<in> modificationOrder T rho x)}"

definition sbUnion where
"sbUnion sb' Tid = {(a,b) . (\<exists> x \<in> Tid . (a,b) \<in> the (sb' x))}"

lemma sbRfMosAcyclic : "\<forall> Tid T rho sb rf Locs . validExecution Tid T rho sb rf \<and>
             acqRelAbove T rho \<longrightarrow> acyclic ((moUnion T rho Locs) \<union> sbUnion sb Tid \<union> rf)"
  sorry



(* definition and proof of the sat of SeqCst ops, atomicity is guaranteed since we do not 
   split rmw to two different ops. 
   Only need for coherence, sc and no-thin-air *)

definition onlySeq where
"onlySeq T rho = (\<forall> a tid aid ac or . a \<in> T \<and> rho a = Some (tid,aid,ac) \<and> acOrder ac = Some or
                     \<longrightarrow> or = SeqCst)"

definition rb where
"rb T rho rf' Locs = relcomp (converse rf') (moUnion T rho Locs)"

definition eco where
"eco T rho rf' Locs = trancl ((rb T rho rf' Locs) \<union> rf' \<union> (moUnion T rho Locs))"

fun rseMyModel where
"rseMyModel rho a b =
    (sameThread rho a b \<or> isRMWInTuple (rho b))"

fun rsMyModel where
"rsMyModel T rho mo' a_rel b =
   (isRelWrite rho a_rel \<and>
    ((b = a_rel) \<or>
      (rseMyModel rho a_rel b \<and> (a_rel,b) \<in> mo' \<and>
        (\<forall> c \<in> T . ((a_rel,c) \<in> mo' \<and> (c,b) \<in> mo') \<longrightarrow> rseMyModel rho a_rel c))))"

fun rsMyModelSet where
"rsMyModelSet T rho Locs =
 {(a,b) . a \<in> T \<and> b \<in> T \<and> rsMyModel T rho (moUnion T rho Locs) a b}"

fun hrsMyModel where
"hrsMyModel T rho mo' a b =
   ((a = b) \<or>
      (rseMyModel rho a b \<and> (a,b) \<in> mo' \<and> 
        (\<forall> c \<in> T . ((a,c) \<in> mo' \<and> (c,b) \<in> mo') \<longrightarrow> rseMyModel rho a c)))"

fun hrsMyModelSet where
"hrsMyModelSet T rho Locs =
  {(a,b) . a \<in> T \<and> b \<in> T \<and> hrsMyModel T rho (moUnion T rho Locs) a b}"

fun swMyModel where
"swMyModel T rho sb' rf' rs hrs a b =
    (sameLocInTuple rho a b \<and>
     (( isRelWrite rho a \<and> isAcqRead rho b \<and> \<not> (sameThread rho a b) \<and>
          (\<exists> c \<in> T . (a,c) \<in> rs \<and> (c,b) \<in> rf' )) \<or>
        (\<not> (sameThread rho a b) \<and>
          isRealFenceInTuple rho a \<and> isRelWrite rho a \<and> isRealFenceInTuple rho b \<and> isAcqRead rho b \<and>
          (\<exists> x \<in> T . (\<exists> y \<in> T . sameLocInTuple rho x y \<and>
              isAtomicInTuple rho x \<and> isAtomicInTuple rho y \<and> isWriteInTuple (rho x) \<and>
              (a,x) \<in> sb' \<and> (y,b) \<in> sb' \<and>
              (\<exists> z \<in> T . (x,z) \<in> hrs \<and> (z,y) \<in> rf')))) \<or> 
        (\<not> (sameThread rho a b) \<and>
          isRealFenceInTuple rho a \<and> isRelWrite rho a \<and> isAtomicInTuple rho b \<and> isAcqRead rho b \<and>
          (\<exists> x \<in> T . sameLocInTuple rho x b \<and>
            isAtomicInTuple rho x \<and> isWriteInTuple (rho x) \<and> (a,x) \<in> sb' \<and>
            (\<exists> z \<in> T . (x,z) \<in> hrs \<and> (z,b) \<in> rf' ) ) ) \<or>
        (\<not> (sameThread rho a b) \<and>
          isAtomicInTuple rho a \<and> isRelWrite rho a \<and>
          isRealFenceInTuple rho b \<and> isAcqRead rho b \<and>
          (\<exists> x \<in> T . sameLocInTuple rho a x \<and> isAtomicInTuple rho x \<and>
            (x,b) \<in> sb' \<and>
            (\<exists> z \<in> T . (a,z) \<in> rs \<and> (z,x) \<in> rf' ) ) )))"

fun swMyModelSet where
"swMyModelSet T rho sb' rf' Locs =
 {(a,b) . a \<in> T \<and> b \<in> T \<and> swMyModel T rho sb' rf' (rsMyModelSet T rho Locs) (hrsMyModelSet T rho Locs) a b}"

fun hbMyModelSet where
"hbMyModelSet T rho sb' rf' Locs = trancl (sb' \<union> swMyModelSet T rho sb' rf' Locs)"


lemma coherence : "\<forall> Tid T rho sb rf Locs . validExecution Tid T rho sb rf \<and> acqRelAbove T rho
                    \<longrightarrow> (\<forall> a \<in> T . (a,a) \<notin> (relcomp (hbMyModelSet T rho (sbUnion sb Tid) rf Locs) (eco T rho rf Locs)))"
  sorry

lemma noThinAir : "\<forall> Tid T rho sb rf Locs . validExecution Tid T rho sb rf \<and>
             acqRelAbove T rho \<longrightarrow> acyclic (sbUnion sb Tid \<union> rf)"
  apply simp
  sorry




end

end