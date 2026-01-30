'''Python is a language within the paradigm of Imperative programming. When I write 
code in python, I like to imagine a little tiny dude living inside my computer,
hopping through my code, line by line, executing commands one by one when I hit run. 
The dude has access to a ginormous filing cabinet somewhere in my computer's circuitous 
depths representing the "memory", or the computer's state, and with every command, he 
retrieves/updates data from the cabinet, essentially modifying the state of the computer.'''

x = 5
print(x)

x = x + 5
print(x + 5)

'''As such, variables are mutable - once you assign them, they can be changed by simply 
reassigning. Another consequence of imperative programming is that since lines of code 
are executed one by one, python will only catch an error when it reaches the erroneous 
line of code. Consider the following:'''

def main():
    password = input("enter your password: \n")
    fifth = password[4]
    print(fifth)


main()

'''If the user enters a password that has fewer than 5 characters, the above code will 
throw an error! In this way, Python's ability to modify the computer's state and interact
 with users becomes it's downfall!

Consider the following - it does the something similar, but instead of printing, it returns.
It also changes the value of a global variable somewhere'''

count = 0

def get_nth_char_password(n : int) -> str : 
    password = input("enter your password: \n")
    count  = count + 1
    nth = password[n]
    return nth

'''The type signature of this function is int -> str, but just the type signature doesn't 
tell us everything the function does. In between, it talks to a user by leaving the internal 
world of python, and it changes the state of the computer. This goes beyond the scope of the
type signature, and so we call them "side effects". What's more, there is no guarantee that
this code won't throw an error in some situations! 

As we will discuss, Lean is NOT like this.'''