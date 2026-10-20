module

public import GMCExplicitDelta.Certificates.Group1Rows
public import GMCExplicitDelta.Certificates.Group2Two
public import GMCExplicitDelta.Certificates.Group2Three
public import GMCExplicitDelta.Certificates.Group2Four
public import GMCExplicitDelta.Certificates.Group3Rows
public import GMCExplicitDelta.Certificates.Group4Rows

/-!
# The numeric obligations of the three certified rows

Each row's `Row.Obligations` is assembled field by field from the four certificate groups:
group 1 (source constants, sphere, Stirling, parameters, band, fin), group 2 (history, averaging,
bad charge), group 3 (geometry, barrier, planar derivative test), group 4 (fresh returns and seeds).
-/

@[expose] public section

open GMCExplicitDelta.Contract

namespace GMCExplicitDelta.Certificates

/-- All numeric obligations of `rowTwo`. -/
theorem rowTwo_obligations_proof : rowTwo.Obligations :=
  have g1 := rowTwo_group1
  have g2 := rowTwo_group2
  have g3 := rowTwo_group3
  have g4 := rowTwo_group4
  { src1 := g1.src1, src2 := g1.src2, src3 := g1.src3, src4 := g1.src4, src5 := g1.src5,
    src6 := g1.src6, src7 := g1.src7, avg1 := g1.avg1, avg2 := g1.avg2, sph := g1.sph,
    par1 := g1.par1, par2 := g1.par2, par3 := g1.par3, par4 := by norm_num [rowTwo],
    hist1 := g2.hist1, hist2 := g2.hist2, avg4 := g2.avg4, avg5 := g2.avg5,
    bad1 := g2.bad1, bad2 := g2.bad2,
    geo1 := g3.geo1, geo2 := g3.geo2, var1 := g1.var1, geo4 := g3.geo4,
    bar1 := g3.bar1, bar2 := g3.bar2, fin1 := g1.fin1, band1 := g1.band1,
    ret1 := g4.ret1, ret2 := g4.ret2, ret3 := g4.ret3, ret4 := g4.ret4 }

/-- All numeric obligations of `rowThree`. -/
theorem rowThree_obligations_proof : rowThree.Obligations :=
  have g1 := rowThree_group1
  have g2 := rowThree_group2
  have g3 := rowThree_group3
  have g4 := rowThree_group4
  { src1 := g1.src1, src2 := g1.src2, src3 := g1.src3, src4 := g1.src4, src5 := g1.src5,
    src6 := g1.src6, src7 := g1.src7, avg1 := g1.avg1, avg2 := g1.avg2, sph := g1.sph,
    par1 := g1.par1, par2 := g1.par2, par3 := g1.par3, par4 := by norm_num [rowThree],
    hist1 := g2.hist1, hist2 := g2.hist2, avg4 := g2.avg4, avg5 := g2.avg5,
    bad1 := g2.bad1, bad2 := g2.bad2,
    geo1 := g3.geo1, geo2 := g3.geo2, var1 := g1.var1, geo4 := g3.geo4,
    bar1 := g3.bar1, bar2 := g3.bar2, fin1 := g1.fin1, band1 := g1.band1,
    ret1 := g4.ret1, ret2 := g4.ret2, ret3 := g4.ret3, ret4 := g4.ret4 }

/-- All numeric obligations of `rowFour`. -/
theorem rowFour_obligations_proof : rowFour.Obligations :=
  have g1 := rowFour_group1
  have g2 := rowFour_group2
  have g3 := rowFour_group3
  have g4 := rowFour_group4
  { src1 := g1.src1, src2 := g1.src2, src3 := g1.src3, src4 := g1.src4, src5 := g1.src5,
    src6 := g1.src6, src7 := g1.src7, avg1 := g1.avg1, avg2 := g1.avg2, sph := g1.sph,
    par1 := g1.par1, par2 := g1.par2, par3 := g1.par3, par4 := by norm_num [rowFour],
    hist1 := g2.hist1, hist2 := g2.hist2, avg4 := g2.avg4, avg5 := g2.avg5,
    bad1 := g2.bad1, bad2 := g2.bad2,
    geo1 := g3.geo1, geo2 := g3.geo2, var1 := g1.var1, geo4 := g3.geo4,
    bar1 := g3.bar1, bar2 := g3.bar2, fin1 := g1.fin1, band1 := g1.band1,
    ret1 := g4.ret1, ret2 := g4.ret2, ret3 := g4.ret3, ret4 := g4.ret4 }

end GMCExplicitDelta.Certificates
