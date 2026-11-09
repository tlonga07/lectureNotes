// #Sireum #Logika
//@Logika: --manual
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//YOU DO THIS:
//Add deduce blocks so each assert holds.

//Do not change anbthing in the program or asserts.


var a: Z = Z.prompt("Enter a an integer between 5-10: ")
var b: Z = Z.prompt("Enter a an integer between 5-10: ")
var c: Z = Z.prompt("Enter a an integer between 5-10: ")

val aOrig: Z = a

assume(a >= 5)
assume(a <= 10)
assume(b >= 5)
assume(b <= 10)
assume(c >= 5)
assume(c <= 10)

a = a + b

Deduce(
    1 ( a == Old(a) + b ) by Premise, 
    2 ( aOrig == Old(a)) by Premise,
    3 ( a == aOrig + b ) by Subst_>(2, 1),

    4 ( b >= 5) by Premise,
    5 ( Old(a) >= 5) by Premise,
    6 ( a >= 10 ) by Algebra*(1, 4, 5),

    7 ( b <= 10 ) by Premise, 
    8 ( Old(a) <= 10 ) by Premise, 
    9 ( a <= 20 ) by Algebra*(1, 7, 8),

    10 ( a >= 10 & a <=20 ) by AndI(6, 9) 
)
assert(a == aOrig + b) //say a equals original a + b
assert(a >= 10 & a <= 20) //get a to be greater than or equal to 10 AND smaller than or equal to twenty
///

a = a + c

Deduce(
    1 ( a == Old(a) + c ) by Premise, 
    2 ( Old(a) == aOrig + b ) by Premise,
    3 ( a == aOrig + b + c ) by Subst_<(2, 1), 
    
    4 ( Old(a) >= 10 & Old(a) <= 20 ) by Premise, 
    5 ( Old(a) >= 10 ) by AndE1(4), 
    6 ( Old(a) <= 20 ) by AndE2(4), 
    7 ( c >= 5 ) by Premise, 
    8 ( c <= 10) by Premise,
    9 ( a >= 15 ) by Algebra*(1, 5, 7),
    10 ( a <= 30 ) by Algebra*(1, 6, 8),

    11 ( a >= 15 & a <= 30 ) by AndI(9, 10)
) 



assert(a == aOrig + b + c) //prove a = old(a) which is greater than 10 smaller than 20
assert(a >= 15 & a <= 30)