import { makeFaqs } from './FaqData';

export const findFAQById = id => {
  makeFaqs().forEach(question => {
    if (question.id === id) {
      return question;
    }
  });
  return undefined;
};

export const findAllFrequentlyAskedQuestions = () => makeFaqs();

export const createFAQ = data => data;
