import React from 'react';
import FAQAnswerService from '../../services/FAQAnswerService';
import FAQAnswerDetailInfo from './FAQAnswerDetailInfo';

class FAQAnswerDetails extends React.Component {
  constructor(props) {
    super(props);
    this.faqAnswerService = FAQAnswerService.getInstance();
    this.state = {
      faqAnswers: [],
      faqAnswer: {
        question: '',
        answer: '',
        id: 1,
      },
    };
  }
  componentDidMount() {
    this.faqAnswerService.findAllFAQAnswers().then(faqAnswers => {
      this.props.history.push('/admin/faas/' + faqAnswers[0].id);
      this.setState({
        faqAnswers: faqAnswers,
        faqAnswer: faqAnswers[0],
      });
    });
  }
  selectFAQAnswer = id =>
    this.faqAnswerService.findFAQAnswerById(id).then(faqAnswer => {
      this.props.history.push('/admin/faas/' + id);
      this.setState({
        faqAnswer: faqAnswer,
      });
    });
  render() {
    return (
      <div>
        <FAQAnswerDetailInfo
          faqAnswer={this.state.faqAnswer}
          faqAnswers={this.state.faqAnswers}
          onChange={this.selectFAQAnswer}
        />
      </div>
    );
  }
}

export default FAQAnswerDetails;
