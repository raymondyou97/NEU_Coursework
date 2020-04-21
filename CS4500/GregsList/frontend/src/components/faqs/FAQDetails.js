import React from 'react';
import FAQService from '../../services/FAQService';
import FAQDetailInfo from './FAQDetailInfo';

class FAQDetails extends React.Component {
  constructor(props) {
    super(props);
    this.faqService = FAQService.getInstance();
    this.state = {
      faqs: [],
      faq: {
        title: '',
        id: 1,
        question: '',
      },
    };
  }
  componentDidMount() {
    this.faqService
      .findAllFrequentlyAskedQuestions(0, '', '', '')
      .then(faqs => {
        this.props.history.push('/admin/faqs/' + faqs.content[0].id);
        this.setState({
          faqs: faqs.content,
          faq: faqs.content[0],
        });
      });
  }
  selectFAQ = id =>
    this.faqService.findFAQById(id).then(faq => {
      this.props.history.push('/admin/faqs/' + id);
      this.setState({
        faq: faq,
      });
    });
  render() {
    return (
      <div>
        <h3>Frequently Asked Question Details</h3>
        <FAQDetailInfo
          faqs={this.state.faqs}
          faq={this.state.faq}
          onChange={this.selectFAQ}
        />
      </div>
    );
  }
}

export default FAQDetails;
