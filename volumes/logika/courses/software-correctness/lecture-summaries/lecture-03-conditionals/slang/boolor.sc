// #Sireum #Logika
import org.sireum._

var a: B = randomInt() > 0
var b: B = randomInt() > 0

if (!a || b) {
  a = !a
} else {
  a = !b
}
assert(a | b)