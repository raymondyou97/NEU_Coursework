import faas from './frequently_asked_answers.mock.json';

export const findFAQAnswerById = id => {
  faas.forEach(ans => {
    if (ans.id === id) {
      return ans;
    }
  });
  return undefined;
};

export const findAllFAQAnswers = () => faas;
