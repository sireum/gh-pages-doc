// #Sireum #Logika
import org.sireum._

val m: Z = randomInt()
val n: Z = randomInt()
var x: Z = m
var y: Z = n

{
  val t = x
  x = y
  y = t
}

assert(x == n & y == m)