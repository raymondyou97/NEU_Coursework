export const makeFaq = (id = 0) => ({
  id,
  title: `Question #${id}`,
  question: 'What is your favorite color?',
});

// Builds an array of FAQs of the given size by calling makeFaq
export const makeFaqs = (size = 5) =>
  [...Array(size)].map((_, i) => makeFaq(i));
