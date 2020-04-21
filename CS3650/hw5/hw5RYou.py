Python 3.6.2 (v3.6.2:5fd33b5, Jul  8 2017, 04:57:36) [MSC v.1900 64 bit (AMD64)] on win32
Type "copyright", "credits" or "license()" for more information.
>>> Raymond You
CS3650 Systems - Cooperman
HW5

Part 1:

-Python > List-1 > sum3
	def sum3(nums):
		return sum(nums)

-Python > List-1 > rotate_left3
	def rotate_left3(nums):
		return nums[1:] + nums[0:1]
  
-Python > List-1 > max_end3
	def max_end3(nums):
		return [max(nums[0], nums[2]),max(nums[0], nums[2]),max(nums[0], nums[2])]

-Python > List-1 > make_ends
	def make_ends(nums):
		return [nums[0], nums.pop()]

-Python > List-1 > has23
	def has23(nums):
		return 2 in nums or 3 in nums
  
-Python > List-2 > count_events
	def count_evens(nums):
		return len([n for n in nums if n % 2 == 0])

-Python > List-2 > sum13
	def sum13(nums):
		return sum([nums[i] for i in range(len(nums)) if not (nums[i] == 13 or (nums[i-1] == 13 and i > 0))])

 Python > List-2 > big_diff
	def big_diff(nums):
		return max(nums) - min(nums)

-Python > List-2 > sum67
 
	def sum67(nums):
		while 6 in nums:
			rest = nums[nums.index(6):]
			nums = nums[:nums.index(6)] + rest[rest.index(7)+1:]
		return sum(nums)
 
-Python > List-2 > centered_average
	def centered_average(nums):
		return (sum(nums) - max(nums) - min(nums)) / (len(nums) - 2)

-Python > List-2 > has22
	def has22(nums):
		return sum(1 for i in range(len(nums) - 1) if nums[i] == nums[i+1] == 2) > 0 

-Python > String-1 > extra_end 
	def extra_end(str):
		return 3 * str[-2:]

-Python > String-1 > without_end 
	def without_end(str):
		return str[1:-1]

-Python > String-2 > double_char
	def double_char(str):
		return ''.join(str[i] * 2 for i in range(len(str)))
		
-Python > String-2 > count_code
	def count_code(str):
		return len([i for i in range(len(str)) if i < len(str) - 3 and str[i:i+2] == "co" and str[i+3] == "e"])

-Python > String-2 > count_hi
    def count_hi(str):
		return str.count("hi")

-Python > String-2 > end_other
	def end_other(a, b):
		return a.lower().endswith(b.lower()) or b.lower().endswith(a.lower()) 

-Python > String-2 > cat_dog
    def cat_dog(str):
		return str.count("cat") == str.count("dog")

-Python > String-2 > xyz_there
	def xyz_there(str):
		return (str.count('xyz') - str.count('.xyz')) >= 1
		
Part 2:
-Python > counts lines, words, and chars
def word_count(string):
	return [string.count('\n'), len([words for words in string.split(' ')]), len(string)]

-Python > counts the number of times each digit occurs, the number of times a whitespace occurs, and the number of other characters.
def count_digits(string):
	mycount = [string.count(c) for c in "0123456789 \t\n" ]
	return "digits = " + ' '.join(str(c) for c in mycount[0:10]) + "; white space = " + str(mycount[10]) + "; other = " + str(len(string)+1 - sum(mycount))