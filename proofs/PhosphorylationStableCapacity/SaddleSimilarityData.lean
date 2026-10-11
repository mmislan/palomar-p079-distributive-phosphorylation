module
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixCertificates
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

def saddleT : ScaledIntegerMatrix (Fin 6) (Fin 6) :=
  ⟨1000, !![547, 1000, -5, 745, 212, 968;
    1000, -393, 66, 587, -114, 512;
    1000, -526, 74, 529, -401, 724;
    391, 702, 103, -397, 1000, -238;
    -598, -576, -123, 97, 1000, 648;
    706, 742, 1000, 976, 991, 772]⟩

def saddleU : ScaledIntegerMatrix (Fin 6) (Fin 6) :=
  ⟨412660228651468303, !![-31395330886441000, 194298102084664000, 128522920621678000, 233232451396800000, -95190276648613000, -58222694039674000;
    219488932427618000, -192449597793567000, -20310862225379000, 55099714073948000, -125908163575918000, -5859852748263000;
    -323388199478624000, -943060622554836000, 770141533801959000, -12505617766556000, -117161696959607000, 403172005145273000;
    110942160973398000, 1359109887872348000, -1293625983374351000, -426536838333744000, -9670112527436000, 49325651482495000;
    -31797284248756000, 443776103045018000, -383298357216390000, 140609580099246000, 170342735534402000, 5385238932307000;
    137207350781916500, -1059053892014423000, 1031890642208778000, 108698678203273500, 153391539584254000, 1894881617338000]⟩

def saddleA : ScaledIntegerMatrix (Fin 6) (Fin 6) :=
  ⟨528134750, !![-1482222000, 0, 1067315750, 1385606750, 1152884750, 1323751875;
    0, -1227136625, 0, 883121250, 941996000, 1470130750;
    -7598226636, -7598226636, -10101748636, -9363770136, -7598226636, -7598226636;
    857472000, 0, -857472000, -2268728000, 0, 0;
    624750000, 0, 0, 0, -3313436000, -624750000;
    0, 1227136625, 0, 0, -941996000, -2169132625]⟩

def saddleB : ScaledIntegerMatrix (Fin 6) (Fin 6) :=
  ⟨435880413387572098675658500, !![2165391052014398595857765, -1355999605460115849134310, 1715004893543442407034700, 228104222461189183584175, 466282695951845873784520, -3695266821109606651247640;
    -296177945413579888012898, -1280098011690367657334472458, -111588743285218125599090, 126877753605450536782190, 36450815910337749975436, -305234202644674804354402;
    414802006900290771389728, -97829389925719323407612, -1521200487370197575469656260, -256372649692312982312840, 216532262096209513106504, 2189046166055976295726572;
    460503904777353034184091, -148326875866442364582514, 107429983224865473523780, -2278634154236812497823677855, -439902024883288578159312, 1295549579204492038428384;
    1957345326872474669590594, 4192016455689668142608524, -3647378711419853915897480, -394272692000142149767570, -3486206990793599559873872608, 1302676307900244603334056;
    -3582708492900649714359250, -2907648548949961570173000, 5310693073173391070227500, 2248665837468602563291250, -1323555730697697438259000, -8406598325402237854520229500]⟩


-- Exact producer identities; `decide` computes only closed integer arithmetic.
theorem saddleTU_integer : saddleT.entries * saddleU.entries =
    ((saddleT.denominator : ℤ) * (saddleU.denominator : ℤ)) •
      (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide

theorem saddleUT_integer : saddleU.entries * saddleT.entries =
    ((saddleU.denominator : ℤ) * (saddleT.denominator : ℤ)) •
      (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide

theorem saddleTAB_cross_integer :
    (saddleB.denominator : ℤ) •
      ((saddleT.entries * saddleA.entries) * saddleU.entries) =
    ((saddleT.denominator * saddleA.denominator * saddleU.denominator : ℕ) : ℤ) •
      saddleB.entries := by decide

theorem saddleTU_real : saddleT.realMatrix * saddleU.realMatrix = 1 := by
  apply ScaledIntegerMatrix.inverse_of_integer_product saddleT saddleU
  · decide
  · decide
  · exact saddleTU_integer

theorem saddleUT_real : saddleU.realMatrix * saddleT.realMatrix = 1 := by
  apply ScaledIntegerMatrix.inverse_of_integer_product saddleU saddleT
  · decide
  · decide
  · exact saddleUT_integer

theorem saddleTAB_real :
    saddleT.realMatrix * saddleA.realMatrix * saddleU.realMatrix =
      saddleB.realMatrix := by
  rw [ScaledIntegerMatrix.realMatrix_mul, ScaledIntegerMatrix.realMatrix_mul]
  apply ScaledIntegerMatrix.realMatrix_eq_of_integer_cross_product
  · decide
  · decide
  · exact saddleTAB_cross_integer

theorem saddleB_charpoly_eq_saddleA :
    saddleB.realMatrix.charpoly = saddleA.realMatrix.charpoly := by
  rw [← saddleTAB_real, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    saddleUT_real, Matrix.one_mul]

end
end PhosphorylationStableCapacity
