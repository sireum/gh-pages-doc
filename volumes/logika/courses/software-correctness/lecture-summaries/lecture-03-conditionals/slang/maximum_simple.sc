// #Sireum #Logika
import org.sireum._
val x: Z = randomInt()
val y: Z = randomInt()

var z: Z = 0
if (x < y) {
  z = y
} else {
  z = x
}
assert(z == x | z == y)
assert(y <= z & x <= z)