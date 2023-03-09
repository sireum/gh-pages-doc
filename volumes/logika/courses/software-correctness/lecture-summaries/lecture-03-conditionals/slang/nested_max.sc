// #Sireum #Logika
import org.sireum._
val x: Z = randomInt(); val y: Z = randomInt(); val z: Z = randomInt()
var m: Z = 0

if (x < y) {
  if (y < z) {
    m = z
  } else {
    m = y
  }
} else {
  if (x < z) {
    m = z
  } else {
    m = x
  }
}

assert(m == x | m == y | m == z)
assert(x <= m & y <= m & z <= m)