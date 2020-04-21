import React from 'react';
import ServiceMultipleChoiceQuestion from './ServiceMultipleChoiceQuestion';
import ServiceTrueFalseQuestion from './ServiceTrueFalseQuestion';

const findAnswer = (question, answers) => {
  return answers.find(element => {
    return question.id === element.serviceQuestion.id;
  });
};

const ServiceQuestion = ({ question, answers }) => (
  <div className="col-6">
    {question.type === 'TrueFalse' && (
      <ServiceTrueFalseQuestion
        question={question}
        answer={findAnswer(question, answers)}
      />
    )}
    {question.type === 'MultipleChoice' && (
      <ServiceMultipleChoiceQuestion
        question={question}
        answer={findAnswer(question, answers)}
      />
    )}
  </div>
);

export default ServiceQuestion;
