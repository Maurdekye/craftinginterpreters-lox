use crate::run;

#[test]
fn resolver() {
    assert!(run(r#"
var a = "global";
{
  fun showA() {
    print a;
  }

  showA();
  var a = "block";
  showA();
  print "a: " + a;
}"#
    .to_owned())
    .is_ok());
}

#[test]
fn classes() {
    assert!(run(r#"
class DevonshireCream {
    serveOn() {
        return "Scones";
    }
}

print DevonshireCream;"#
        .to_owned())
    .is_ok());
}

#[test]
fn instance() {
    assert!(run(r#"
class Bagel {}
var bagel = Bagel();
print bagel;"#
        .to_owned())
    .is_ok());
}

#[test]
fn fields() {
    assert!(run(r#"
class Bagel {}
var bagel = Bagel();
bagel.topping = "cream cheese";
bagel.seed = "poppy";

print "my " + bagel.seed + " seed bagel is topped with " + bagel.topping;
"#
    .to_owned())
    .is_ok());
}

#[test]
fn methods() {
    assert!(run(r#"
class Bacon {
    eat() {
        print "Crunch crunch crunch!";
    }
}

Bacon().eat();
"#
    .to_owned())
    .is_ok())
}

#[test]
fn this() {
    assert!(run(r#"
class Cake {
    taste() {
        var adjective = "delicious";
        print "The " + this.flavor + " cake is " + adjective + "!";
    }
}

var cake = Cake();
cake.flavor = "German chocolate";
cake.taste();
"#
    .to_owned())
    .is_ok())
}

#[test]
fn init() {
    assert!(run(r#"
class Foo {
    init() {
        print this;
    }
}

var foo = Foo();
print foo.init();
"#
    .to_owned())
    .is_ok())
}

#[test]
fn class_method() {
    assert!(run(r#"
class Math {
    class square(n) {
        return n * n;
    }
}

print Math.square(3);
"#
    .to_owned())
    .is_ok())
}

#[test]
fn getters() {
    assert!(run(r#"
class Circle {
  init(radius) {
    this.radius = radius;
  }

  area {
    return 3.141592653 * this.radius * this.radius;
  }
}

var circle = Circle(4);
print circle.area;
"#
    .to_owned())
    .is_ok())
}

#[test]
fn inheritance() {
    assert!(run(r#"
class Doughnut {
  cook() {
    print "Fry until golden brown.";
  }
}

class BostonCream < Doughnut {}

BostonCream().cook();
    "#
    .to_owned())
    .is_ok());
}

#[test]
fn super_keyword() {
    assert!(run(r#"
class Doughnut {
  cook() {
    print "Fry until golden brown.";
  }
}

class BostonCream < Doughnut {
  cook() {
    super.cook();
    print "Pipe full of custard and coat with chocolate.";
  }
}

BostonCream().cook();
    "#
    .to_owned())
    .is_ok());
}
