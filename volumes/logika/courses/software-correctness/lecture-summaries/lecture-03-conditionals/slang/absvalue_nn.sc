// #Sireum #Logika
import org.sireum._
val x: Z = randomInt()
var y: Z = randomInt()

assume(x != 0)
if (x < 0) {
  y = -x
} else {
  y = x
}

assert(x/y == 1 | x/y == -1)
assert(y >= 0)