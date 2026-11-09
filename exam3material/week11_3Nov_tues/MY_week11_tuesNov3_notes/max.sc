// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//get 2 user inputs: x and y
//assume that x > y
//set a max variable to x
//want to assert that max is the biggest of our two inputs

val x: Z = Z.prompt("Enter first number: ")
val y: Z = Z.prompt("Enter second number: ")

//x = 3, y = 4

//how do we assume x is bigger than y?


val max: Z = x


//what can we put in a proof block here?

//how do we assert max is the biggest between our two inputs?
