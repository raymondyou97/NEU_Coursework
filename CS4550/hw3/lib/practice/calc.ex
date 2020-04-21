defmodule Practice.Calc do
  def parse_float(text) do
    {num, _} = Float.parse(text)
    num
  end

  # Hint:
  # expr
  # |> split
  # |> tag_tokens  (e.g. [+, 1] => [{:op, "+"}, {:num, 1.0}]
  # |> convert to postfix
  # |> reverse to prefix
  # |> evaluate as a stack calculator using pattern matching

  # This should handle +,-,*,/ with order of operations,
  # but doesn't need to handle parens.
  def calc(inputExpression) do
    inputExpression
    #split into list with each individual index while removing spaces
    |> String.split(" ")
    #map operations to proper operations and numbers to numbers
    |> Enum.map_every(1, &Practice.Calc.convertToTagTokens/1)
    #throw onto stack while converting to postfix
    |> Practice.Calc.convertToPostfix([], [])
    #finally evaluate as everything should be in correct order
    |> Practice.Calc.evaluateExpression([])
  end

  def convertToTagTokens(input) do
    case input do
      #operator
      "+" ->
        {:operator, "+"}
      "-" ->
        {:operator, "-"}
      "*" ->
        {:operator, "*"}
      "/" ->
        {:operator, "/"}
      #number, parse to floating point
      _ ->
        {:num, parse_float(input)}
    end
  end

  @moduledoc """
  Infix to postfix algorithm taken from http://csis.pace.edu/~wolf/CS122/infix-postfix.htm
  1.	Print operands as they arrive.
  2.	If the stack is empty or contains a left parenthesis on top, push the incoming operator onto the stack.
  ...
  5.	If the incoming symbol has higher precedence than the top of the stack, push it on the stack.
  6.	If the incoming symbol has equal precedence with the top of the stack, use association.
      If the association is left to right, pop and print the top of the stack and then push the incoming operator.
      If the association is right to left, push the incoming operator.
  7.	If the incoming symbol has lower precedence than the symbol on the top of the stack, pop the stack and print the top operator.
      Then test the incoming operator against the new top of stack.
  8.	At the end of the expression, pop and print all operators on the stack. (No parentheses should remain.)
  """
  #recursive, accumulator function
  def convertToPostfix(list, accumulator, stack) do
    lengthOfList = length(list)
    #empty list, finish
    if (lengthOfList == 0) do
      accumulator ++ stack
    #still converting
    else
      input = hd(list)
      case input do
        #if keyword list :num
        {:num, number} ->
          newNumber = [{:num, number}]
          newAccumulator = accumulator ++ newNumber
          convertToPostfix(tl(list), newAccumulator, stack)
        #if keywordlist :operator
        {:operator, operator} ->
          #when stack is empty, push operator onto stack
          lengthOfStack = length(stack)
          if (lengthOfStack == 0) do
            convertToPostfix(tl(list), accumulator, [{:operator, operator}])
          else
            #if incoming operator is higher precedence that current stuff on stack, push on stack
            if (isHigherPrecedence(operator, elem(hd(stack), 1))) do
              convertToPostfix(tl(list), accumulator, [{:operator, operator}] ++ stack)
            #incoming operator is less precedence, so move operator from stack to accumulator and add new operator to stack
            else
              convertToPostfix(tl(list), accumulator ++ stack, [{:operator, operator}])
            end
          end
        end
    end
  end

  #logic flow could be better here but works
  def isHigherPrecedence(firstOperation, secondOperation) do
    # multiplication always highest
    if(firstOperation == "*") do
      true
    else
      if(firstOperation == "/") do
        # divide higher than others
        if(secondOperation == "+" || secondOperation == "-") do
          true
        end
      else
        if(firstOperation == "+") do
          # add higher than subtract
          if(secondOperation == "-") do
            true
          #rest doesn't matter
          else
            false
          end
        else
          false
        end
      end
    end
  end

  #finally evaluate the expression
  def evaluateExpression(list, stack) do
    lengthOfList = length(list)
    #finished, return final value
    if(lengthOfList == 0) do
      Enum.at(stack, 0)
    #keep evaluating
    else
      input = hd(list)
      firstNumber = Enum.at(stack, 1)
      secondNumber = Enum.at(stack, 0)
      case input do
        #operator cases (PEMDAS)
        {:operator, "*"} ->
          product = firstNumber * secondNumber
          rest = tl(tl(stack))
          evaluateExpression(tl(list), [product] ++ rest)
        {:operator, "/"} ->
          dividend = firstNumber / secondNumber
          rest = tl(tl(stack))
          evaluateExpression(tl(list), [dividend] ++ rest)
        {:operator, "+"} ->
          sum = firstNumber + secondNumber
          rest = tl(tl(stack))
          evaluateExpression(tl(list), [sum] ++ rest)
        {:operator, "-"} ->
          difference = firstNumber - secondNumber
          rest = tl(tl(stack))
          evaluateExpression(tl(list), [difference] ++ rest)
        #found number, add to stack
        {:num, number} ->
          evaluateExpression(tl(list), [number] ++ stack)
        end
      end
    end

end
