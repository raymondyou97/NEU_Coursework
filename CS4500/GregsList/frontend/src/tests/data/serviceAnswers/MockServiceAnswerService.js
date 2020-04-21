'use es6';

import { SERVICE_ANSWER_LIST } from './ServiceAnswerData';

export const mockFindServiceAnswerById = id => {
  SERVICE_ANSWER_LIST.forEach(answer => {
    if (answer.id === id) {
      return answer;
    }
  });
  return [];
};

export const mockFindAllServiceAnswers = () => {
  return SERVICE_ANSWER_LIST;
};

export const mockFindPagedServiceAnswer = (page, count) => {
  return SERVICE_ANSWER_LIST.slice(0, count);
};

export const mockDeleteServiceAnswer = id => {
  return { status: 200 };
};

export const mockCreateServiceAnswer = data => {
  return data;
};

export const mockUpdateServiceAnswer = (id, data) => {
  SERVICE_ANSWER_LIST.forEach(answer => {
    if (answer.id === id) {
      let newAnswer = Object.assign(answer, data);
      return newAnswer;
    }
  });
  return data;
};
