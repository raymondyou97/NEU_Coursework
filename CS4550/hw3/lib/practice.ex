defmodule Practice do
  @moduledoc """
  Practice keeps the contexts that define your domain
  and business logic.

  Contexts are also responsible for managing your data, regardless
  if it comes from the database, an external API or others.
  """

  def double(x) do
    2 * x
  end

  def factor(x) do
    Practice.Factor.factor(x)
  end

  def calc(x) do
    Practice.Calc.calc(x)
  end

  def palindrome(x) do
    reverse = String.reverse(x)
    x == reverse
  end
end
