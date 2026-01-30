from typing import Callable

'''inspired by https://www.youtube.com/watch?v=C2w45qRc3aU&t=685s 
(Studying With Alex - The Absolute Best Intro to Monads For Software Engineers)'''

# def square(x: int) -> int :
#     return x * x

# def addOne(x: int) -> int : 
#     return x + 1

# print(addOne(square(2)))

'''say we want to do the same thing as above, but also record a log of the results. 
Perhaps we want the output to contain the following:
    {value : 5, log: ["squared 2 to get 4", "added 1 to 4 to get 5"]}
'''

class IntWithLogs:
    def __init__(self, value: int, log: list):
        self.value = value
        self.log = log

def square(x : int) -> IntWithLogs :
    value = x * x 
    log = ["squared {} to get {}".format(x, x * x)]
    return IntWithLogs(value, log) 

def addOne(x : IntWithLogs) -> IntWithLogs: 
    value = x.value + 1
    log = x.log
    log.append("added 1 to {} to get {}".format(x.value, x.value + 1))
    return IntWithLogs(value, log)

print(addOne(square(2)).value)
print(addOne(square(2)).log)

'''But we have an issue:'''

square(square(2))
addOne(5)



'''we create a new function that wraps an int into the IntWithLogs format'''

def wrapWithLogs(x : int) -> IntWithLogs :
    return IntWithLogs(x, [])

'''and a new run function that takes 
- an IntWithLogs 
- a function that takes ints and returns an IntWithLogs
 unwraps the IntWithLogs, and applies the function, ...'''

def runWithLogs(input : IntWithLogs, transform : Callable[[int], IntWithLogs]) -> IntWithLogs:
    output = transform(input.value)
    value = output.value
    log = input.log + output.log

    return IntWithLogs(value, log)

# '''we now rewrite the square and add functions accordingly'''

def square(x : int) -> IntWithLogs :
    value = x * x 
    log = ["squared {} to get {}".format(x, x * x)]
    return IntWithLogs(value, log) 

def addOne(x : int) -> IntWithLogs : 
    value = x + 1
    log = ["added 1 to {} to get {}".format(x, x + 1)]
    return IntWithLogs(value, log)

a = wrapWithLogs(2)
b = runWithLogs(a, square)
c = runWithLogs(b, addOne)

print(c.value)
print(c.log)


'''We just wrote a Monad! It's a useful code design tool that allows us to chain 
operations and abstract away busy work. Every monad has 3 things:
1) A wrapper type (intWithLogs)
2) A wrap funciton (wrapWithLogs) that wrap the data into the monad wrapper type
    The wrap function is often called "pure", "return", or "unit" - we'll see this later
3) A run function that runs transformations on wrapped values by unwrapping them.
    The run function is often called "bind", ">>=" or in lean, "do" '''