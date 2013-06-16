var A = {
    foo: 5
};

A.foo = 4;


var B = {
    foo: 5
}

B.foo = 4;


label:
for (var i=9; i<10; i++) {
    notLabel:
    if (true) {
        break label;
    }
    if (false) {
        continue label;
    }
    function f() {
        label:
        while(true) {
            break label;
        }
    }
}