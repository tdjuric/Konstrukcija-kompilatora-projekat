// test function
fun fib(x: int) {    
    if (x < 3.0){
        1 + 0;
    } else {
        fib(x - 1) + fib(x - 2);
    };
}

fib(5.0);