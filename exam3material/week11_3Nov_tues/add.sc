// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

///(add.sc)
//Example: write a program that creates a number, x, with value 2

//Create a value, y, that is initialized to x + 2

//We want to assert at the end that y is 4

///

val x: Z = 2

//What can we put in a proof block here?
//Do we need this step? 


val y: Z = x + 2

Deduce (
    1 ( y == x + 2 ) by Premise,
    2 ( x == 2 ) by Premise,
    3 ( y == 4 ) by Algebra*(1,2)
    //need: y == 4
)



//what can we put in a proof block here?

assert(y == 4)



