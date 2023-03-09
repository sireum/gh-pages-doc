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
z = z - x
assert(z == 0 | z == y - x)
