defmodule Practice.Factor do
  #variable for base prime number
  @basePrimeNumber 2

  def factor(number) do
    #Only valid for numbers: 2 or more, return empty list if not valid
    if(number < @basePrimeNumber) do
      []
    #continue with function
    else
      primeFactors = findFactors([], number, @basePrimeNumber)
      #need commas between factors to pass test cases
      Enum.join(primeFactors, ", ")
    end
  end

  #simple prime number checker, returns boolean
  def isPrimeNumber(number, divider) do
    remainder = rem(number, divider)
    if(remainder == 0) do
      true
    else
      false
    end
  end

  def findFactors(accumulator, number, divider) do
    #found divisible number, add to accumuator
    if (number <= divider) do
      accumulator ++ [number]
    #continue into helper method
    else
      primeFactorHelp(accumulator, number, divider)
    end
  end

  #helper method
  def primeFactorHelp(accumulator, number, divider) do
    #not a prime number here
    if (!isPrimeNumber(number, divider)) do
      #keep recursing until divider == num or divisible
      findFactors(accumulator, number, divider + 1)
    #prime number
    else
      #add divider to accumulator
      newAccumulator = accumulator ++ [divider]
      #get new dividend
      newDividend = div(number, divider)
      #recurse with new accumulator and new dividend
      findFactors(newAccumulator, newDividend, @basePrimeNumber)
    end
  end
end
