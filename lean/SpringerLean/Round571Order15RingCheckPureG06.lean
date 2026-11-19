import SpringerLean.Round711OrderedScaledAdd
import SpringerLean.Round695ClearedSumSoundness
import SpringerLean.Round570Order15RingDataG06L00
import SpringerLean.Round570Order15RingDataG06L01
import SpringerLean.Round570Order15RingDataG06L02
import SpringerLean.Round570Order15RingDataG06L03
import SpringerLean.Round570Order15RingDataG06L04
import SpringerLean.Round570Order15RingDataG06L05
import SpringerLean.Round570Order15RingDataG06L06
import SpringerLean.Round570Order15RingDataG06L07
import SpringerLean.Round570Order15RingDataG06L08
import SpringerLean.Round570Order15RingDataG06L09
import SpringerLean.Round570Order15RingDataG06L10
import SpringerLean.Round570Order15RingDataG06N0411
import SpringerLean.Round570Order15RingDataG06N0412
import SpringerLean.Round570Order15RingDataG06N0413
import SpringerLean.Round570Order15RingDataG06N0414
import SpringerLean.Round570Order15RingDataG06N0415
import SpringerLean.Round570Order15RingDataG06N0416
import SpringerLean.Round570Order15RingDataG06N0417
import SpringerLean.Round570Order15RingDataG06N0418
import SpringerLean.Round570Order15RingDataG06N0419
import SpringerLean.Round570Order15RingDataG06N0420
import SpringerLean.Round571Order15RingCheckPureG06Leaf0010
import SpringerLean.Round622PureGramIdentity
import SpringerLean.Round558FastPolynomialSoundness

namespace SpringerLean
open RatPolyCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem order15RingTreeG06N0411_identity :
    rawCoeffExprIdentity order15RingTreeG06N0411.polynomial (.add order15RingTreeG06L00.polynomial order15RingTreeG06L01.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 3032039294109289004319239940561600000000
    order15RingTreeG06N0411.polynomial order15RingTreeG06L00.polynomial order15RingTreeG06L01.polynomial (by decide +kernel)


theorem order15RingTreeG06N0412_identity :
    rawCoeffExprIdentity order15RingTreeG06N0412.polynomial (.add order15RingTreeG06L02.polynomial order15RingTreeG06L03.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 176064968646398111956576401551479701846634567093931263404404539200000000
    order15RingTreeG06N0412.polynomial order15RingTreeG06L02.polynomial order15RingTreeG06L03.polynomial (by decide +kernel)


theorem order15RingTreeG06N0413_identity :
    rawCoeffExprIdentity order15RingTreeG06N0413.polynomial (.add order15RingTreeG06L04.polynomial order15RingTreeG06L05.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 997999216472485706429515495735421038392421259560849641456795925360499733712441261410095882129890327680000000
    order15RingTreeG06N0413.polynomial order15RingTreeG06L04.polynomial order15RingTreeG06L05.polynomial (by decide +kernel)


theorem order15RingTreeG06N0414_identity :
    rawCoeffExprIdentity order15RingTreeG06N0414.polynomial (.add order15RingTreeG06L06.polynomial order15RingTreeG06L07.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 8117616495371563443879802601027228351323097051028830787685666001392883281513155976521427898719708271488508456489265229839779145951218059453440000000
    order15RingTreeG06N0414.polynomial order15RingTreeG06L06.polynomial order15RingTreeG06L07.polynomial (by decide +kernel)


theorem order15RingTreeG06N0415_identity :
    rawCoeffExprIdentity order15RingTreeG06N0415.polynomial (.add order15RingTreeG06L08.polynomial order15RingTreeG06L09.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 1680436694531773053292213005491098255929629346442475450082083331881783850531389577818905083553275665315244022123547671345487588306679613287026519301806234591826702691533613171578271219825765209679964160000000
    order15RingTreeG06N0415.polynomial order15RingTreeG06L08.polynomial order15RingTreeG06L09.polynomial (by decide +kernel)


theorem order15RingTreeG06N0416_identity :
    rawCoeffExprIdentity order15RingTreeG06N0416.polynomial (.add order15RingTreeG06N0411.polynomial order15RingTreeG06N0412.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 210400804151338972901682578420018467439664840388800000000
    order15RingTreeG06N0416.polynomial order15RingTreeG06N0411.polynomial order15RingTreeG06N0412.polynomial (by decide +kernel)


theorem order15RingTreeG06N0417_identity :
    rawCoeffExprIdentity order15RingTreeG06N0417.polynomial (.add order15RingTreeG06N0413.polynomial order15RingTreeG06N0414.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 11809528032030811394387793046630750151918547566832905867013626947991095984135917874138783297268248790830049796318865446413091840000000
    order15RingTreeG06N0417.polynomial order15RingTreeG06N0413.polynomial order15RingTreeG06N0414.polynomial (by decide +kernel)


theorem order15RingTreeG06N0418_identity :
    rawCoeffExprIdentity order15RingTreeG06N0418.polynomial (.add order15RingTreeG06N0415.polynomial order15RingTreeG06L10.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 5934676361468731537493772716140676579639512591257803529197252342736135150829253380704327135921989878186661085670522840320686463280581777565808640000000
    order15RingTreeG06N0418.polynomial order15RingTreeG06N0415.polynomial order15RingTreeG06L10.polynomial (by decide +kernel)


theorem order15RingTreeG06N0419_identity :
    rawCoeffExprIdentity order15RingTreeG06N0419.polynomial (.add order15RingTreeG06N0416.polynomial order15RingTreeG06N0417.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 2181420831007678159468495344413994586364468875876225678728881523224385546244460223397029258240000000
    order15RingTreeG06N0419.polynomial order15RingTreeG06N0416.polynomial order15RingTreeG06N0417.polynomial (by decide +kernel)


theorem order15RingTreeG06N0420_identity :
    rawCoeffExprIdentity order15RingTreeG06N0420.polynomial (.add order15RingTreeG06N0419.polynomial order15RingTreeG06N0418.polynomial) := by
  intro env
  exact OrderedScaledAdd.check_sound env coeffExprVariableOrder 229019994245915768737657220392831291235940218003429049355037412495375360000000
    order15RingTreeG06N0420.polynomial order15RingTreeG06N0419.polynomial order15RingTreeG06N0418.polynomial (by decide +kernel)

end SpringerLean
