'use es6';

import { SERVICE_QUESTION_LIST } from './ServiceQuestionData';

export const mockDeleteService = id => {
  return { status: 200 };
};

export const mockFindServiceById = id => {
  SERVICE_QUESTION_LIST.forEach(question => {
    if (question.id === id) {
      return question;
    }
  });
  return [];
};

export const mockFindAllServices = () => {
  return SERVICE_QUESTION_LIST;
};

export const mockCreateService = data => {
  return data;
};

export const mockUpdateService = (id, data) => {
  SERVICE_QUESTION_LIST.forEach(question => {
    if (question.id === id) {
      let newQuestion = Object.assign(question, data);
      return newQuestion;
    }
  });
  return data;
};
